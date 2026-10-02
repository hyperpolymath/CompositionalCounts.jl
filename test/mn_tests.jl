# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# MN regression, pure-Julia backend (no R). The MGLM comparison lives in test/r/.

using CompositionalCounts: mn_derivs, mn_loglik, mn_coef, softmax!
using Random

"""
    rmultinomial(rng, N, p) -> Vector{Int}

One multinomial draw of size `N` over probabilities `p`, by sequential binomials
built from uniform draws (no Distributions.jl dependency).
"""
function rmultinomial(rng::AbstractRNG, N::Integer, p::AbstractVector)
    y = zeros(Int, length(p))
    c = cumsum(p)
    for _ in 1:N
        u = rand(rng) * c[end]
        y[searchsortedfirst(c, u)] += 1
    end
    return y
end

"""
    simulate_mn(rng, B, X; Nrange) -> Matrix{Int}

Counts from the MN model with full coefficient matrix `B` (reference column zero)
and design `X`; sample totals uniform on `Nrange`.
"""
function simulate_mn(rng::AbstractRNG, B::AbstractMatrix, X::AbstractMatrix; Nrange=400:600)
    n, J = size(X, 1), size(B, 2)
    Y = zeros(Int, n, J)
    p = zeros(J)
    for i in 1:n
        softmax!(p, X[i, :]' * B |> vec)
        Y[i, :] .= rmultinomial(rng, rand(rng, Nrange), p)
    end
    return Y
end

"""
    fd_gradient_ok(gradfun, B, Y, X, free; h=1e-5, rtol=1e-5) -> Bool

Compare `gradfun(B, Y, X, free)` with central finite differences of `mn_loglik`
over θ = vec(B[:, free]).
"""
function fd_gradient_ok(gradfun, B, Y, X, free; h=1e-5, rtol=1e-5)
    p, J = size(B)
    θ = vec(B[:, free])
    g = gradfun(B, Y, X, free)
    fd = similar(θ)
    for k in eachindex(θ)
        e = zeros(length(θ)); e[k] = h
        fd[k] = (mn_loglik(mn_coef(θ .+ e, p, J, free), Y, X) -
                 mn_loglik(mn_coef(θ .- e, p, J, free), Y, X)) / (2h)
    end
    return maximum(abs, g .- fd) <= rtol * max(1.0, maximum(abs, fd))
end

const BTRUE = [ 0.5 -0.3  0.8  0.2 0.0;
                0.4  0.0 -0.6  0.3 0.0;
               -0.2  0.5  0.0 -0.4 0.0]          # p = 3, J = 5, reference 5

"""
    design(rng, n) -> Matrix

Intercept, one standard-normal covariate and one balanced binary covariate.
"""
design(rng, n) = hcat(ones(n), randn(rng, n), Float64.(isodd.(1:n)))

@testset "MN (Julia backend)" begin
    rng = Xoshiro(17)
    X = design(rng, 300)
    Y = simulate_mn(rng, BTRUE, X)
    free = 1:4 |> collect

    @testset "analytic gradient = central finite differences" begin
        B = mn_coef(0.1 .* randn(Xoshiro(3), 12), 3, 5, free)
        good(B, Y, X, f) = mn_derivs(B, Y, X, f; info=false)[2]
        @test fd_gradient_ok(good, B, Y, X, free)
        # positive control: one flipped component must be caught
        bad(B, Y, X, f) = (g = copy(good(B, Y, X, f)); g[5] = -g[5]; g)
        @test !fd_gradient_ok(bad, B, Y, X, free)
    end

    @testset "fit contract" begin
        f = fit(MN, Y, X; reference=5)
        @test f.status === :inference
        @test f.reference == 5
        @test all(iszero, f.coef[:, 5])
        @test all(ismissing, f.se[:, 5])
        @test f.tested == [false, true, true]
        @test all(ismissing, f.clr_p[1, :]) && all(!ismissing, f.clr_p[2, :])
        @test maximum(abs, sum(f.clr; dims=2)) <= 1e-12
        @test f.provenance.convergence.converged
        @test occursin("PRDS", only(f.provenance.caveats))
        # reference invariance of the CLR effects
        g = fit(MN, Y, X; reference=1)
        @test maximum(abs, f.clr .- g.clr) <= 1e-8
        @test f.loglik ≈ g.loglik rtol = 1e-10
    end

    @testset "zero-count cells are fine (only all-zero taxa refuse)" begin
        Y0 = copy(Y); Y0[1:40, 2] .= 0
        @test fit(MN, Y0, X; reference=5).status === :inference
    end

    @testset "planted truth: ≥95% of coefficients within 3 SE" begin
        hits = 0; total = 0
        for seed in 1:20
            r = Xoshiro(1000 + seed)
            Xs = design(r, 300)
            fs = fit(MN, simulate_mn(r, BTRUE, Xs), Xs; reference=5)
            z = abs.(fs.coef[:, 1:4] .- BTRUE[:, 1:4]) ./ fs.se[:, 1:4]
            hits += count(<=(3), z); total += length(z)
        end
        @test hits / total >= 0.95
    end

    @testset "L1 penalty: estimation only" begin
        fp = fit(MN, Y, X; reference=5, penalty=5.0)
        @test fp.status === :penalised_no_inference
        @test all(ismissing, fp.se) && all(ismissing, fp.clr_p) && all(ismissing, fp.clr_q)
        @test maximum(abs, sum(fp.clr; dims=2)) <= 1e-12
        big = fit(MN, Y, X; reference=5, penalty=1e6)
        @test all(iszero, big.coef[2:3, :])            # slopes shrunk to 0 …
        @test any(!iszero, big.coef[1, :])             # … intercept unpenalised
        tiny = fit(MN, Y, X; reference=5, penalty=1e-9)
        @test maximum(abs, tiny.coef .- fit(MN, Y, X; reference=5).coef) <= 1e-4
    end

    @testset "refusals (one per row of the refusal table)" begin
        @test_throws InvalidCounts fit(MN, [1 -1 2; 2 2 2; 3 1 1; 2 2 2], ones(4, 1))
        @test_throws InvalidCounts fit(MN, [1.5 1 2; 2 2 2; 3 1 1; 2 2 2], ones(4, 1))
        @test_throws InvalidCounts fit(MN, [0 0 0; 2 2 2; 3 1 1; 2 2 2], ones(4, 1))
        @test_throws UnidentifiableTaxon fit(MN, [1 0 2; 2 0 2; 3 0 1; 2 0 2], ones(4, 1))
        @test_throws RankDeficientDesign fit(MN, Y, hcat(X, X[:, 2]))
        @test_throws RankDeficientDesign fit(MN, Y[1:3, :], X[1:3, :])
        Yr = copy(Y); Yr[11:end, 3] .= 0                       # taxon 3 prevalence < 0.5
        @test_throws InvalidReference fit(MN, Yr, X; reference=3)
        # quasi-complete separation: taxon 3 absent exactly when x = 0
        xs = Float64.(isodd.(1:60))
        Ys = hcat(fill(50, 60), fill(30, 60), ifelse.(xs .== 1, 20, 0))
        @test_throws NonConvergence fit(MN, Ys, hcat(ones(60), xs); reference=1)
        # R backend without RCall loaded: typed refusal, no silent switch to :julia
        @test_throws BackendUnavailable fit(MN, Y, X; backend=:r)
        @test_throws ArgumentError fit(MN, Y, X; penalty=-1.0)
    end
end
