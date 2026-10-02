# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

using LinearAlgebra: dot, cholesky, Symmetric, issuccess, norm, diag, kron, inv
using SpecialFunctions: loggamma, logbeta, digamma, trigamma
using Random: Xoshiro, randn

const DM_MAXIT = 500
const DM_BOUNDARY_APLUS = 1e6     # documented convention, calibrated in test/dm_tests.jl
const DM_STOP_APLUS = 1e10        # iterate is heading to the multinomial boundary: stop
const DM_STARTS = 8
const DM_PERTURB = 0.5            # start perturbation, in standard deviations of each column
const DM_SAME_LL = 1e-6           # relative log-likelihood tie for MultipleOptima
const DM_SAME_COEF = 1e-2         # coefficient distance for MultipleOptima, in standard errors (calibrated: start jitter ≤ 4.3e-4 SE)
const DM_EXACT_SUM = 50           # counts up to this use exact digamma/trigamma sums

"""
    lgamma_rise(a, y)

log Γ(a + y) − log Γ(a) for a > 0 and integer-valued y ≥ 0, computed through
`logbeta` so that it stays accurate when a ≫ y (the near-multinomial regime).
"""
lgamma_rise(a::Real, y::Real) = y == 0 ? 0.0 : loggamma(y) - logbeta(a, y)

"""
    digamma_rise(a, y)

ψ(a + y) − ψ(a) for integer-valued y ≥ 0: the exact sum Σₖ 1/(a + k) for small y,
the digamma difference otherwise.
"""
function digamma_rise(a::Real, y::Real)
    y == 0 && return 0.0
    y <= DM_EXACT_SUM || return digamma(a + y) - digamma(a)
    s = 0.0
    for k in 0:(Int(y) - 1)
        s += 1 / (a + k)
    end
    return s
end

"""
    trigamma_fall(a, y)

ψ′(a) − ψ′(a + y) for integer-valued y ≥ 0: the exact sum Σₖ 1/(a + k)² for small y,
the trigamma difference otherwise.
"""
function trigamma_fall(a::Real, y::Real)
    y == 0 && return 0.0
    y <= DM_EXACT_SUM || return trigamma(a) - trigamma(a + y)
    s = 0.0
    for k in 0:(Int(y) - 1)
        s += 1 / (a + k)^2
    end
    return s
end

"""
    dm_loglik(B, Y, X) -> Float64

Dirichlet-Multinomial log-likelihood (without the multinomial constant) at
coefficients `B` (p × J), α = exp(XB). Returns `-Inf` where α is not finite.
"""
function dm_loglik(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix)
    α = exp.(X * B)
    all(isfinite, α) || return -Inf
    ll = 0.0
    for i in axes(Y, 1)
        A = sum(@view α[i, :])
        N = sum(@view Y[i, :])
        ll -= lgamma_rise(A, N)
        for j in axes(Y, 2)
            ll += lgamma_rise(α[i, j], Y[i, j])
        end
    end
    return ll
end

"""
    dm_derivs(B, Y, X; info=true) -> (ll, g, I, D, α)

Log-likelihood (without constant), gradient g = vec(XᵀD) with respect to
θ = vec(B), where Dᵢⱼ = αᵢⱼ[ψ(yᵢⱼ+αᵢⱼ) − ψ(αᵢⱼ) − ψ(Nᵢ+α₊ᵢ) + ψ(α₊ᵢ)], and, when
`info`, the observed information Σᵢ Wᵢ ⊗ xᵢxᵢᵀ with
Wᵢ = −(αᵢαᵢᵀ[ψ′(α₊ᵢ) − ψ′(α₊ᵢ+Nᵢ)] + diag(Dᵢ − αᵢ²[ψ′(αᵢ) − ψ′(αᵢ+yᵢ)])).
Also returns D and α = exp(XB).
"""
function dm_derivs(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix; info::Bool=true)
    n, J = size(Y)
    p = size(X, 2)
    α = exp.(X * B)
    D = zeros(n, J)
    Imat = info ? zeros(p * J, p * J) : zeros(0, 0)
    W = zeros(J, J)
    ll = 0.0
    for i in 1:n
        αi = @view α[i, :]
        A = sum(αi)
        N = sum(@view Y[i, :])
        ll -= lgamma_rise(A, N)
        v = digamma_rise(A, N)
        for j in 1:J
            ll += lgamma_rise(αi[j], Y[i, j])
            D[i, j] = αi[j] * (digamma_rise(αi[j], Y[i, j]) - v)
        end
        if info
            t = trigamma_fall(A, N)
            for k in 1:J, j in 1:J
                W[j, k] = -αi[j] * αi[k] * t
            end
            for j in 1:J
                W[j, j] -= D[i, j] - αi[j]^2 * trigamma_fall(αi[j], Y[i, j])
            end
            xi = @view X[i, :]
            Imat .+= kron(W, xi * xi')
        end
    end
    return ll, vec(X' * D), Imat, D, α
end

"""
    common_scale_direction(X) -> Vector

The p-vector w with Xw = 1: adding c·w to every column of B multiplies every α
by eᶜ (the overdispersion direction). Throws [`UnidentifiableDispersion`](@ref)
when the constant vector is not in the column space of `X`.
"""
function common_scale_direction(X::AbstractMatrix)
    n = size(X, 1)
    w = X \ ones(n)
    norm(X * w .- 1) <= 1e-8 * sqrt(n) || throw(UnidentifiableDispersion(
        "DM needs the constant vector in the column space of X (an intercept): " *
        "otherwise the common scale of α, which carries the overdispersion, is not a free direction"))
    return w
end

"""
    dm_identifiable(Y, X)

Throw [`UnidentifiableDispersion`](@ref) when fewer than p samples have Nᵢ ≥ 2
(a total of 1 is a categorical draw, which carries no information on the scale of α).
"""
function dm_identifiable(Y::AbstractMatrix, X::AbstractMatrix)
    p = size(X, 2)
    m = count(>=(2), sum(Y; dims=2))
    m >= p || throw(UnidentifiableDispersion(
        "only $m samples have total ≥ 2; DM needs at least p = $p to identify the scale of α"))
    return nothing
end

"""
    dm_mom_start(Y, X, ref, w) -> Matrix

Method-of-moments start: proportions from the MN fit (coefficients centred across
taxa, so the start — and hence the DM fit — is the same for every `ref`), ρ̂ from the Pearson
statistic, E X² ≈ Σᵢ (J−1)(1 + (Nᵢ−1)ρ), then α₊ = 1/ρ̂ − 1 applied along the
common-scale direction `w`. ρ̂ is clamped to [1e-4, 0.5].
"""
function dm_mom_start(Y::AbstractMatrix, X::AbstractMatrix, ref::Int, w::AbstractVector)
    n, J = size(Y)
    Bmn = try
        mn_newton(Y, X, ref)[2]
    catch e
        e isa NonConvergence || rethrow()
        throw(NonConvergence("DM start (the MN fit behind the method-of-moments start) failed: " * e.msg))
    end
    Bmn = Bmn .- sum(Bmn; dims=2) ./ J     # centred: the start no longer depends on `ref`
    η = X * Bmn
    P = zeros(J)
    X2 = 0.0
    lse = zeros(n)
    Nm1 = 0.0
    for i in 1:n
        Ni = sum(@view Y[i, :])
        softmax!(P, @view η[i, :])
        lse[i] = logsumexp(@view η[i, :])
        X2 += sum((Y[i, :] .- Ni .* P) .^ 2 ./ (Ni .* P))
        Nm1 += Ni - 1
    end
    ρ = clamp((X2 - n * (J - 1)) / ((J - 1) * max(Nm1, 1.0)), 1e-4, 0.5)
    shift = log(1 / ρ - 1) - sum(lse) / n
    return Bmn .+ shift .* w
end

"""
    dm_ascent(Y, X, B0, w) -> NamedTuple

Modified-Newton ascent on the DM log-likelihood from `B0`: the observed
information is shifted by τI until positive definite (the surface is not concave),
with Armijo backtracking. Never throws on numerical trouble; returns `status`:

- `:converged` — Newton decrement ≤ $(NEWTON_TOL)·(1 + |ll|) with no shift;
- `:runaway`   — after ascent steps, max α₊ passed $(DM_STOP_APLUS): the iterate
  ran to the multinomial boundary, where ψ′ differences are below float precision
  and the slope sign is noise, so no slope condition is applied;
- `:boundary`  — converged with max α₊ >
  $(DM_BOUNDARY_APLUS) while the likelihood still rises along the common scale `w`;
- `:diverged`  — after ascent steps, a fitted expected count Nᵢαᵢⱼ/α₊ᵢ fell below
  $(MN_MIN_EXPECTED) (separation). There is no raw |β| cap: it is not invariant to
  the location and scale of the design columns;
- `:stalled` / `:maxit` — line search failure or $(DM_MAXIT) iterations.
"""
function dm_ascent(Y::AbstractMatrix, X::AbstractMatrix, B0::AbstractMatrix, w::AbstractVector)
    p, J = size(B0)
    θ = vec(copy(B0))
    ll = -Inf
    dec = Inf
    for it in 1:DM_MAXIT
        B = reshape(θ, p, J)
        ll, g, Imat, D, α = dm_derivs(B, Y, X)
        Aplus = vec(sum(α; dims=2))
        result(status) = (status=status, B=copy(B), ll=ll, info=Imat, D=D, alpha_plus=Aplus,
                          iterations=it - 1, newton_decrement=dec, max_abs_gradient=maximum(abs, g),
                          scale_slope=sum(D))
        it > 1 && maximum(Aplus) > DM_STOP_APLUS && return result(:runaway)
        it > 1 && dm_min_expected(Y, α) < MN_MIN_EXPECTED && return result(:diverged)
        S = Symmetric((Imat + Imat') / 2)
        F = cholesky(S; check=false)
        τ = 0.0
        while !issuccess(F)
            τ = τ == 0 ? 1e-8 * max(1.0, maximum(abs, diag(S))) : 10τ
            τ > 1e20 && return result(:stalled)
            F = cholesky(Symmetric(S + τ * Id(size(S, 1))); check=false)
        end
        Δ = F \ g
        dec = dot(g, Δ) / 2
        if τ == 0 && dec <= NEWTON_TOL * (1 + abs(ll))
            r = result(:converged)
            if maximum(Aplus) > DM_BOUNDARY_APLUS && r.scale_slope > 0
                return merge(r, (status=:boundary,))
            end
            return r
        end
        t = 1.0
        accepted = false
        for _ in 1:60
            θn = θ .+ t .* Δ
            lln = dm_loglik(reshape(θn, p, J), Y, X)
            if isfinite(lln) && lln >= ll + 1e-4 * t * dot(g, Δ) - 4eps() * abs(ll)
                θ = θn
                accepted = true
                break
            end
            t /= 2
        end
        accepted || return result(:stalled)
    end
    B = reshape(θ, p, J)
    ll, g, Imat, D, α = dm_derivs(B, Y, X)
    return (status=:maxit, B=copy(B), ll=ll, info=Imat, D=D, alpha_plus=vec(sum(α; dims=2)),
            iterations=DM_MAXIT, newton_decrement=dec, max_abs_gradient=maximum(abs, g),
            scale_slope=sum(D))
end

"""
    dm_min_expected(Y, α) -> Float64

The smallest fitted expected count Nᵢαᵢⱼ/α₊ᵢ over all samples and taxa.
"""
function dm_min_expected(Y::AbstractMatrix, α::AbstractMatrix)
    m = Inf
    for i in axes(Y, 1)
        m = min(m, sum(@view Y[i, :]) * minimum(@view α[i, :]) / sum(@view α[i, :]))
    end
    return m
end

"""
    dm_starts(X, B0, w, nstarts) -> (starts, seeds)

The method-of-moments start `B0` followed by `nstarts − 1` perturbations of it,
start k drawn from `Xoshiro(k)`. Perturbations are $(DM_PERTURB) per unit of each
*centred, standardised* non-constant column, with the centring absorbed along the
common-scale direction `w`, plus $(DM_PERTURB) on each taxon's level; so a start
moves log α by O(1) at the data, whatever the columns' location and scale.
"""
function dm_starts(X::AbstractMatrix, B0::AbstractMatrix, w::AbstractVector, nstarts::Integer)
    n, p = size(X)
    J = size(B0, 2)
    constcol = constant_columns(X)
    seeds = collect(1:(nstarts - 1))
    starts = [copy(B0)]
    for s in seeds
        rng = Xoshiro(s)
        K = zeros(p, J)
        level = DM_PERTURB .* randn(rng, J)
        for r in 1:p
            constcol[r] && continue
            c = @view X[:, r]
            m = sum(c) / n
            sd = sqrt(sum(abs2, c .- m) / max(n - 1, 1))
            δ = DM_PERTURB .* randn(rng, J) ./ sd
            K[r, :] .+= δ
            level .-= δ .* m
        end
        push!(starts, B0 .+ K .+ w * level')
    end
    return starts, seeds
end

"""
    dm_select(runs) -> (best index, runner-up gap)

Choose the start with the highest log-likelihood and apply the multistart
refusals: [`BoundaryEstimate`](@ref), [`NonConvergence`](@ref), and
[`MultipleOptima`](@ref) when another converged start ties on log-likelihood
(within $(DM_SAME_LL) relative) but differs in some coefficient by more than
$(DM_SAME_COEF) of that coefficient's standard error at the best start. The check is
skipped when the best start's information is not positive definite, so that
[`SingularInformation`](@ref) is raised downstream instead.
"""
function dm_select(runs::AbstractVector)
    lls = [isfinite(r.ll) ? r.ll : -Inf for r in runs]
    b = argmax(lls)
    best = runs[b]
    if best.status === :runaway
        throw(BoundaryEstimate(
            "DM iterate ran to the multinomial boundary (max α₊ = $(maximum(best.alpha_plus)) > " *
            "$(DM_STOP_APLUS)): no detectable overdispersion — fit MN"))
    elseif best.status === :boundary
        throw(BoundaryEstimate(
            "DM likelihood still increases along the common scale of α at max α₊ = " *
            "$(maximum(best.alpha_plus)) (> $(DM_BOUNDARY_APLUS)): no detectable overdispersion — fit MN"))
    elseif best.status === :diverged
        throw(NonConvergence(
            "DM coefficients diverge: a fitted expected count fell below $(MN_MIN_EXPECTED) " *
            "(quasi-complete separation by a covariate?); the MLE does not exist"))
    elseif best.status !== :converged
        throw(NonConvergence("DM best start ended $(best.status) after $(best.iterations) iterations"))
    end
    F = cholesky(Symmetric(best.info); check=false)
    if issuccess(F)
        se = reshape(sqrt.(diag(inv(F))), size(best.B))
        for (k, r) in enumerate(runs)
            k == b && continue
            r.status === :converged || continue
            dist = maximum(abs.(r.B .- best.B) ./ se)
            if abs(r.ll - best.ll) <= DM_SAME_LL * abs(best.ll) && dist > DM_SAME_COEF
                throw(MultipleOptima(
                    "DM starts $b and $k reach the same log-likelihood with coefficients " *
                    "$(dist) standard errors apart", (best.ll, r.ll), (best.B, r.B)))
            end
        end
    end
    others = [lls[k] for k in eachindex(lls) if k != b]
    gap = isempty(others) ? NaN : best.ll - maximum(others)
    return b, gap
end

"""
    dm_extra(B, Aplus, cov, ref) -> NamedTuple

The DM-specific fields of a fit: fitted α₊ᵢ and ρᵢ = 1/(1 + α₊ᵢ) per sample, and
the log-ratio contrasts βⱼ − β_ref with delta-method SEs from `cov` (the
covariance of vec(B)); the reference column is exactly zero with `missing` SEs.
"""
function dm_extra(B::AbstractMatrix, Aplus::AbstractVector, cov::AbstractMatrix, ref::Int)
    p, J = size(B)
    Dm = Matrix{Float64}(Id(J))
    Dm[ref, :] .-= 1                       # (B Dm)[:, j] = B[:, j] − B[:, ref]
    L = kron(Dm', Matrix{Float64}(Id(p)))
    cse = reshape(sqrt.(max.(diag(L * cov * L'), 0.0)), p, J)
    contrast_se = Matrix{Union{Missing,Float64}}(cse)
    contrast_se[:, ref] .= missing
    return (alpha_plus=collect(Aplus), rho=1 ./ (1 .+ Aplus), contrast=B * Dm,
            contrast_se=contrast_se)
end

"""
    dm_check_estimate(B, Y, X, w) -> (ll, info, D, alpha_plus)

Derivatives at a supplied estimate (e.g. MGLM's), with the same refusals the
Julia solver applies at termination: [`NonConvergence`](@ref) for diverging
coefficients and [`BoundaryEstimate`](@ref) at the multinomial boundary.
"""
function dm_check_estimate(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix, w::AbstractVector)
    ll, _, Imat, D, α = dm_derivs(B, Y, X)
    Aplus = vec(sum(α; dims=2))
    dm_min_expected(Y, α) < MN_MIN_EXPECTED && throw(NonConvergence(
        "DM coefficients diverge: a fitted expected count fell below $(MN_MIN_EXPECTED)"))
    maximum(Aplus) > DM_STOP_APLUS && throw(BoundaryEstimate(
        "DM estimate is at the multinomial boundary (max α₊ = $(maximum(Aplus)) > $(DM_STOP_APLUS)): " *
        "no detectable overdispersion — fit MN"))
    maximum(Aplus) > DM_BOUNDARY_APLUS && sum(D) > 0 && throw(BoundaryEstimate(
        "DM likelihood still increases along the common scale of α at max α₊ = $(maximum(Aplus)): " *
        "no detectable overdispersion — fit MN"))
    return ll, Imat, D, Aplus
end

"""
    _fit_julia(::Type{DM}, Y, X, ref, λ) -> CompositionalFit

Pure-Julia DM fit: method-of-moments start plus $(DM_STARTS - 1) seeded
perturbations, modified-Newton ascent from each, best log-likelihood reported
with the multistart record in provenance. λ > 0 is refused (MN only).
"""
function _fit_julia(::Type{DM}, Y::Matrix{Float64}, X::Matrix{Float64}, ref::Int, λ::Float64)
    λ == 0 || throw(ArgumentError("penalty > 0 is supported for MN only; DM is unpenalised"))
    p, J = size(X, 2), size(Y, 2)
    w = common_scale_direction(X)
    dm_identifiable(Y, X)
    starts, seeds = dm_starts(X, dm_mom_start(Y, X, ref, w), w, DM_STARTS)
    runs = [dm_ascent(Y, X, B0, w) for B0 in starts]
    b, gap = dm_select(runs)
    best = runs[b]
    tested = collect(.!constant_columns(X))
    c = multinomial_constant(Y)
    inf = inference(best.B, Matrix{Float64}(Id(p * J)), best.info, tested; free_cols=1:J)
    report = (converged=true, iterations=best.iterations, newton_decrement=best.newton_decrement,
              max_abs_gradient=best.max_abs_gradient, solver="modified Newton, multistart",
              starts=length(runs), seeds=vcat(0, seeds), best_start=b,
              start_logliks=[r.ll + c for r in runs], start_status=[r.status for r in runs],
              runner_up_gap=gap)
    prov = provenance(:julia, "DM"; reference=ref, penalty=0.0, convergence=report,
                      caveats=("seed 0 is the method-of-moments start; seed k ≥ 1 perturbs it with Xoshiro(k)",))
    return CompositionalFit(DM, best.B, inf.se, inf.clr, inf.clr_se, inf.clr_p, inf.clr_q,
                            tested, best.ll + c, ref, :inference,
                            dm_extra(best.B, best.alpha_plus, inf.cov, ref), prov)
end
