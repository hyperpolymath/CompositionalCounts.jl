# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# DM regression, pure-Julia backend (no R). Uses the helpers of mn_tests.jl
# (included first by runtests.jl). The MGLM comparison lives in test/r/.

using CompositionalCounts: dm_derivs, dm_loglik, dm_select, common_scale_direction, mn_loglik
using LinearAlgebra: I

"""
    rdirmult(rng, N, α) -> Vector{Int}

One Dirichlet-Multinomial draw of size `N` with parameter `α`, by the Pólya urn
(no Distributions.jl dependency).
"""
function rdirmult(rng::AbstractRNG, N::Integer, α::AbstractVector)
    urn = float.(collect(α))
    y = zeros(Int, length(α))
    c = similar(urn)
    for _ in 1:N
        cumsum!(c, urn)
        j = searchsortedfirst(c, rand(rng) * c[end])
        y[j] += 1
        urn[j] += 1
    end
    return y
end

"""
    planted_dm(B, X, ρ) -> Matrix

`B` with its intercept row shifted so the geometric mean of α₊ᵢ over samples is
1/ρ − 1 (ρ = 1/(1 + α₊) is the intra-class correlation).
"""
function planted_dm(B::AbstractMatrix, X::AbstractMatrix, ρ::Real)
    Bd = float.(copy(B))
    η = X * Bd
    Bd[1, :] .+= log(1 / ρ - 1) - sum(log.(sum(exp.(η); dims=2))) / size(X, 1)
    return Bd
end

"""
    simulate_dm(rng, B, X; Nrange) -> Matrix{Int}

Counts from the DM model α = exp(XB); sample totals uniform on `Nrange`.
"""
function simulate_dm(rng::AbstractRNG, B::AbstractMatrix, X::AbstractMatrix; Nrange=400:600)
    α = exp.(X * B)
    Y = zeros(Int, size(α))
    for i in axes(Y, 1)
        Y[i, :] .= rdirmult(rng, rand(rng, Nrange), α[i, :])
    end
    return Y
end

"""
    fd_dm_ok(gradfun, B, Y, X; h=1e-5, rtol=1e-5) -> Bool

Compare `gradfun(B, Y, X)` with central finite differences of `dm_loglik` over vec(B).
"""
function fd_dm_ok(gradfun, B, Y, X; h=1e-5, rtol=1e-5)
    θ = vec(B)
    g = gradfun(B, Y, X)
    fd = similar(θ)
    for k in eachindex(θ)
        e = zeros(length(θ)); e[k] = h
        fd[k] = (dm_loglik(reshape(θ .+ e, size(B)), Y, X) -
                 dm_loglik(reshape(θ .- e, size(B)), Y, X)) / (2h)
    end
    return maximum(abs, g .- fd) <= rtol * max(1.0, maximum(abs, fd))
end

"""
    dm_outcome(Y, X) -> Symbol

`:fit` or the name of the refusal type raised by `fit(DM, Y, X)`.
"""
function dm_outcome(Y, X)
    try
        fit(DM, Y, X; reference=5)
        return :fit
    catch e
        e isa CompositionalCounts.CompositionalError || rethrow()
        return nameof(typeof(e))
    end
end

"""
    fake_run(status, ll, B; info) -> NamedTuple

A hand-made start result with the fields `dm_select` reads.
"""
fake_run(status, ll, B; info=Matrix(1.0I, length(B), length(B))) =
    (status=status, ll=ll, B=B, info=info, alpha_plus=[10.0], iterations=5)

@testset "DM (Julia backend)" begin
    rng = Xoshiro(23)
    X = design(rng, 200)
    BT = planted_dm(BTRUE, X, 0.05)
    Y = simulate_dm(rng, BT, X)

    @testset "analytic gradient and Hessian = central finite differences" begin
        B = BT .+ 0.1 .* randn(Xoshiro(4), size(BT))
        good(B, Y, X) = dm_derivs(B, Y, X; info=false)[2]
        @test fd_dm_ok(good, B, Y, X)
        bad(B, Y, X) = (g = copy(good(B, Y, X)); g[7] = -g[7]; g)      # positive control
        @test !fd_dm_ok(bad, B, Y, X)
        # observed information = −(finite-difference Jacobian of the gradient)
        Imat = dm_derivs(B, Y, X)[3]
        θ = vec(B); h = 1e-5
        H = similar(Imat)
        for k in eachindex(θ)
            e = zeros(length(θ)); e[k] = h
            H[:, k] = (good(reshape(θ .+ e, size(B)), Y, X) .- good(reshape(θ .- e, size(B)), Y, X)) ./ (2h)
        end
        @test maximum(abs, Imat .+ H) <= 1e-5 * maximum(abs, H)
    end

    @testset "DM → MN as α₊ → ∞ along the common scale" begin
        w = common_scale_direction(X)
        gap(c) = abs(dm_loglik(BTRUE .+ c .* w, Y, X) - mn_loglik(BTRUE, Y, X))
        @test gap(20.0) < 1e-3 * gap(5.0)
        @test gap(20.0) < 1e-2
    end

    @testset "fit contract" begin
        f = fit(DM, Y, X; reference=5)
        @test f.status === :inference
        @test f.model === DM
        @test all(!ismissing, f.se)                       # all J columns free (MGLM DM)
        @test f.tested == [false, true, true]
        @test maximum(abs, sum(f.clr; dims=2)) <= 1e-10
        @test f.extra.rho ≈ 1 ./ (1 .+ f.extra.alpha_plus)
        @test all(iszero, f.extra.contrast[:, 5]) && all(ismissing, f.extra.contrast_se[:, 5])
        @test f.extra.contrast[:, 2] ≈ f.coef[:, 2] .- f.coef[:, 5]
        c = f.provenance.convergence
        @test c.starts == 8 && c.seeds == 0:7 && length(c.start_logliks) == 8
        @test f.loglik ≈ maximum(c.start_logliks)
        g = fit(DM, Y, X; reference=1)                    # the fit itself is reference-free
        @test maximum(abs, g.coef .- f.coef) <= 1e-8 && maximum(abs, g.clr .- f.clr) <= 1e-8
    end

    @testset "planted truth at ρ ∈ {0.01, 0.05, 0.2}: ≥95% within 3 SE" begin
        for ρ in (0.01, 0.05, 0.2)
            hits = 0; total = 0
            for seed in 1:20
                r = Xoshiro(4000 + seed)
                Xs = design(r, 200)
                Bs = planted_dm(BTRUE, Xs, ρ)
                fs = fit(DM, simulate_dm(r, Bs, Xs), Xs; reference=5)
                z = abs.(fs.coef .- Bs) ./ fs.se
                hits += count(<=(3), z); total += length(z)
            end
            @test hits / total >= 0.95
        end
    end

    # Boundary calibration (measured 2026-10-02, n = 200, N ∈ 400:600, J = 5, p = 3,
    # seeds 1:40): true-MN data fires BoundaryEstimate 35/40; the other 5 are finite
    # fits at α₊ ∈ [1.3e4, 5.2e5], a genuine finite DM MLE on MN data, which no point
    # threshold on α₊ can refuse. ρ = 0.05 data (α₊ ≈ 25–60) fires 0/40.
    @testset "boundary calibration" begin
        mn = [dm_outcome(simulate_mn(Xoshiro(2000 + s), BTRUE, design(Xoshiro(3000 + s), 200)),
                         design(Xoshiro(3000 + s), 200)) for s in 1:40]
        @test count(==(:BoundaryEstimate), mn) >= 32               # measured 35/40
        @test all(in((:BoundaryEstimate, :fit)), mn)               # nothing else on MN data
        dm = [let Xs = design(Xoshiro(3000 + s), 200)
                  dm_outcome(simulate_dm(Xoshiro(2000 + s), planted_dm(BTRUE, Xs, 0.05), Xs), Xs)
              end for s in 1:40]
        @test all(==(:fit), dm)                                    # measured 40/40
    end

    @testset "multistart selection (hand-made start results)" begin
        B1 = zeros(3, 5); B2 = fill(0.5, 3, 5)
        # two converged starts, tied log-likelihood, coefficients 0.5 SE apart → refuse
        e = try
            dm_select([fake_run(:converged, -100.0, B1), fake_run(:converged, -100.0 - 1e-9, B2)])
        catch err
            err
        end
        @test e isa MultipleOptima
        @test e.loglik == (-100.0, -100.0 - 1e-9) && e.coef == (B1, B2)
        # same optimum to within the tolerance (1e-3 SE apart) → accept the best
        @test dm_select([fake_run(:converged, -100.0, B1),
                         fake_run(:converged, -100.0, B1 .+ 1e-3)])[1] == 1
        # distinct log-likelihoods → the best wins, no refusal
        @test dm_select([fake_run(:converged, -101.0, B1), fake_run(:converged, -100.0, B2)])[1] == 2
        # singular information at the best start → skip, leave SingularInformation to inference
        @test dm_select([fake_run(:converged, -100.0, B1; info=zeros(15, 15)),
                         fake_run(:converged, -100.0, B2)])[1] == 1
        # the best start's status decides the refusal
        @test_throws BoundaryEstimate dm_select([fake_run(:boundary, -99.0, B1), fake_run(:converged, -100.0, B2)])
        @test_throws BoundaryEstimate dm_select([fake_run(:runaway, -99.0, B1)])
        @test_throws NonConvergence dm_select([fake_run(:maxit, -99.0, B1), fake_run(:converged, -100.0, B2)])
        @test_throws NonConvergence dm_select([fake_run(:diverged, -99.0, B1)])
    end

    @testset "refusals" begin
        # no intercept: the common scale of α is not a free direction
        @test_throws UnidentifiableDispersion fit(DM, Y, X[:, 2:3])
        # fewer than p samples with total ≥ 2
        Y1 = zeros(Int, 40, 3)
        Y1[1:30, 1] .= 1; Y1[31:35, 2] .= 1; Y1[36:40, 3] .= 1        # totals of 1 …
        Y1[1, :] .= [2, 1, 1]                                           # … except one sample
        @test_throws UnidentifiableDispersion fit(DM, Y1, hcat(ones(40), Float64.(isodd.(1:40))))
        @test_throws ArgumentError fit(DM, Y, X; penalty=1.0)
        @test_throws BackendUnavailable fit(DM, Y, X; backend=:r)
    end
end
