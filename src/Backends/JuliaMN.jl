# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

using LinearAlgebra: dot, cholesky, Symmetric, isposdef
using SpecialFunctions: loggamma

"""
    multinomial_constant(Y)

Σᵢ [log Nᵢ! − Σⱼ log yᵢⱼ!], the parameter-free part of the multinomial log-likelihood.
"""
multinomial_constant(Y::AbstractMatrix) =
    sum(loggamma(sum(@view Y[i, :]) + 1) for i in axes(Y, 1)) - sum(loggamma.(Y .+ 1))

"""
    mn_coef(θ, p, J, free) -> Matrix

Expand the free parameter vector θ = vec(B[:, free]) to the full p × J matrix with
the reference column fixed at zero.
"""
function mn_coef(θ::AbstractVector, p::Integer, J::Integer, free::AbstractVector{Int})
    B = zeros(p, J)
    B[:, free] .= reshape(θ, p, length(free))
    return B
end

"""
    mn_loglik(B, Y, X) -> Float64

Multinomial log-likelihood (without the constant) at full coefficients `B`.
"""
function mn_loglik(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix)
    η = X * B
    ll = 0.0
    for i in axes(Y, 1)
        ηi = @view η[i, :]
        ll += dot(@view(Y[i, :]), ηi) - sum(@view Y[i, :]) * logsumexp(ηi)
    end
    return ll
end

"""
    mn_derivs(B, Y, X, free; info=true) -> (ll, g, I)

Log-likelihood (without constant), gradient with respect to θ = vec(B[:, free]),
i.e. vec((Xᵀ(Y − N∘P))[:, free]), and, when `info`, the observed (= expected)
information Σᵢ (Nᵢ(diag pᵢ − pᵢpᵢᵀ))[free, free] ⊗ xᵢxᵢᵀ.
"""
function mn_derivs(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix,
                   free::AbstractVector{Int}; info::Bool=true)
    n, J = size(Y)
    p = size(X, 2)
    K = length(free)
    η = X * B
    P = similar(η)
    ll = 0.0
    R = similar(Y, Float64)
    Imat = info ? zeros(p * K, p * K) : zeros(0, 0)
    pi_ = zeros(J)
    for i in 1:n
        ηi = @view η[i, :]
        Ni = sum(@view Y[i, :])
        ll += dot(@view(Y[i, :]), ηi) - Ni * logsumexp(ηi)
        softmax!(pi_, ηi)
        P[i, :] .= pi_
        R[i, :] .= @view(Y[i, :]) .- Ni .* pi_
        if info
            pf = pi_[free]
            W = Ni .* (Diagonal(pf) .- pf * pf')
            xi = @view X[i, :]
            Imat .+= kron(W, xi * xi')
        end
    end
    G = X' * R
    return ll, vec(G[:, free]), Imat
end

using LinearAlgebra: Diagonal

const MN_MAXIT = 200
const MN_DIVERGE = 50.0
const NEWTON_TOL = 1e-12          # relative to 1 + |ll|
const MN_MIN_EXPECTED = 1e-6     # divergence convention, calibrated in test/mn_tests.jl

"""
    check_divergence(B, Y, X)

Throw [`NonConvergence`](@ref) when any fitted expected count Nᵢp̂ᵢⱼ is below
$(MN_MIN_EXPECTED): the signature of coefficients running to ±∞ (e.g. quasi-complete
separation), where the reported "optimum" is only where the optimiser stopped.
"""
function check_divergence(B::AbstractMatrix, Y::AbstractMatrix, X::AbstractMatrix)
    η = X * B
    p = zeros(size(B, 2))
    for i in axes(Y, 1)
        softmax!(p, @view η[i, :])
        m = sum(@view Y[i, :]) * minimum(p)
        m < MN_MIN_EXPECTED && throw(NonConvergence(
            "MN coefficients diverge: fitted expected count $m < $(MN_MIN_EXPECTED) in sample $i " *
            "(quasi-complete separation by a covariate?); the MLE does not exist"))
    end
    return nothing
end

"""
    mn_newton(Y, X, ref) -> (θ, B, ll, info, report)

Damped Newton ascent on the concave MN log-likelihood from θ = 0, stopping when
the Newton decrement gᵀI⁻¹g/2 ≤ $(NEWTON_TOL)·(1 + |ll|), then checking
[`check_divergence`](@ref). Throws [`NonConvergence`](@ref) on
iteration cap, failed line search or coefficient divergence (|β| > $(MN_DIVERGE)),
and [`SingularInformation`](@ref) when the information is not positive definite.
"""
function mn_newton(Y::AbstractMatrix, X::AbstractMatrix, ref::Int)
    J = size(Y, 2)
    p = size(X, 2)
    free = [j for j in 1:J if j != ref]
    θ = zeros(p * length(free))
    for it in 1:MN_MAXIT
        B = mn_coef(θ, p, J, free)
        ll, g, Imat = mn_derivs(B, Y, X, free)
        S = Symmetric((Imat + Imat') / 2)
        isposdef(S) || throw(SingularInformation("MN information not positive definite at iteration $it"))
        Δ = cholesky(S) \ g
        dec = dot(g, Δ) / 2
        if dec <= NEWTON_TOL * (1 + abs(ll))
            check_divergence(B, Y, X)
            report = (converged=true, iterations=it - 1, newton_decrement=dec,
                      max_abs_gradient=maximum(abs, g), solver="damped Newton")
            return θ, B, ll, Imat, report
        end
        t = 1.0
        accepted = false
        for _ in 1:60
            θn = θ .+ t .* Δ
            lln = mn_loglik(mn_coef(θn, p, J, free), Y, X)
            if isfinite(lln) && lln >= ll + 1e-4 * t * dot(g, Δ) - 4eps() * abs(ll)
                θ = θn
                accepted = true
                break
            end
            t /= 2
        end
        accepted || throw(NonConvergence("MN line search failed at iteration $it (decrement $dec)"))
        maximum(abs, θ) > MN_DIVERGE && throw(NonConvergence(
            "MN coefficients diverge (|β| > $(MN_DIVERGE)) — quasi-complete separation by a covariate?"))
    end
    throw(NonConvergence("MN did not converge in $(MN_MAXIT) Newton iterations"))
end

const FISTA_MAXIT = 50_000
const FISTA_TOL = 1e-9

"""
    mn_l1(Y, X, ref, λ, pen) -> (θ, B, ll, report)

L1-penalised MN by FISTA with backtracking and adaptive restart: maximise
ll(θ) − λ Σ |θₖ| over the coordinates flagged in `pen`. Stops when the gradient
mapping (a first-order optimality residual) is ≤ $(FISTA_TOL)·(1 + ΣY).
Throws [`NonConvergence`](@ref) at the iteration cap.
"""
function mn_l1(Y::AbstractMatrix, X::AbstractMatrix, ref::Int, λ::Float64, pen::AbstractVector{Bool})
    J = size(Y, 2)
    p = size(X, 2)
    free = [j for j in 1:J if j != ref]
    f(θ) = -mn_loglik(mn_coef(θ, p, J, free), Y, X)
    grad(θ) = -mn_derivs(mn_coef(θ, p, J, free), Y, X, free; info=false)[2]
    prox(v, s) = [pen[k] ? sign(v[k]) * max(abs(v[k]) - s * λ, 0.0) : v[k] for k in eachindex(v)]
    θ = zeros(p * length(free))
    Ntot = sum(Y)
    z = copy(θ)
    tk = 1.0
    Lc = 1.0
    for it in 1:FISTA_MAXIT
        gz = grad(z)
        fz = f(z)
        local θn
        while true
            θn = prox(z .- gz ./ Lc, 1 / Lc)
            d = θn .- z
            f(θn) <= fz + dot(gz, d) + Lc / 2 * dot(d, d) && break
            Lc *= 2
            Lc > 1e20 && throw(NonConvergence("L1-MN backtracking failed"))
        end
        resid = Lc * maximum(abs, θn .- z)               # gradient mapping at z
        if dot(z .- θn, θn .- θ) > 0                     # momentum overshoot: restart
            z = θn
            tk = 1.0
        else
            tn = (1 + sqrt(1 + 4tk^2)) / 2
            z = θn .+ ((tk - 1) / tn) .* (θn .- θ)
            tk = tn
        end
        θ = θn
        if resid <= FISTA_TOL * (1 + Ntot)
            B = mn_coef(θ, p, J, free)
            return θ, B, mn_loglik(B, Y, X),
                   (converged=true, iterations=it, gradient_mapping=resid, solver="FISTA (L1)")
        end
    end
    throw(NonConvergence("L1-MN did not converge in $(FISTA_MAXIT) FISTA iterations"))
end

"""
    _fit_julia(::Type{MN}, Y, X, ref, λ) -> CompositionalFit

Pure-Julia MN fit: Newton for λ = 0 (with inference), FISTA for λ > 0 (estimates only).
"""
function _fit_julia(::Type{MN}, Y::Matrix{Float64}, X::Matrix{Float64}, ref::Int, λ::Float64)
    n, J = size(Y)
    p = size(X, 2)
    free = [j for j in 1:J if j != ref]
    constcol = constant_columns(X)
    tested = collect(.!constcol)
    c = multinomial_constant(Y)
    if λ == 0
        θ, B, ll, Imat, report = mn_newton(Y, X, ref)
        M = mn_embedding(p, J, free)
        inf = inference(B, M, Imat, tested; free_cols=free)
        status = :inference
    else
        pen = repeat(.!constcol, length(free))
        θ, B, ll, report = mn_l1(Y, X, ref, λ, pen)
        inf = no_inference(B)
        status = :penalised_no_inference
    end
    prov = provenance(:julia, "MN"; reference=ref, penalty=λ, convergence=report)
    return CompositionalFit(MN, B, inf.se, inf.clr, inf.clr_se, inf.clr_p, inf.clr_q,
                            tested, ll + c, ref, status, NamedTuple(), prov)
end

"""
    mn_embedding(p, J, free) -> Matrix

The 0/1 matrix M with vec(B) = M θ, where θ = vec(B[:, free]) and the remaining
column of B is zero.
"""
function mn_embedding(p::Integer, J::Integer, free::AbstractVector{Int})
    M = zeros(p * J, p * length(free))
    for (k, j) in enumerate(free), r in 1:p
        M[(j - 1) * p + r, (k - 1) * p + r] = 1.0
    end
    return M
end
