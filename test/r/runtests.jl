# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# R-backend acceptance tests. Run with R_LIBS_USER pointing at the renv library:
#   julia --project=test/r test/r/runtests.jl
using CompositionalCounts, RCall, Test

R"suppressMessages(library(MGLM)); data(rnaseq)"
const Y = rcopy(Matrix{Float64}, R"as.matrix(rnaseq[,1:6])")
const X = rcopy(Matrix{Float64}, R"model.matrix(~ log(totalReads) + treatment, rnaseq)")

@testset "MN: Julia vs MGLM 0.2.3 on rnaseq" begin
    for ref in (6, 1)
        fj = fit(MN, Y, X; reference=ref)
        fr = fit(MN, Y, X; reference=ref, backend=:r)
        @test fr.provenance.mglm_version == "0.2.3"
        @test maximum(abs, fj.coef .- fr.coef) <= 1e-3
        @test maximum(abs, skipmissing(fj.se .- fr.se)) <= 1e-3
        @test abs(fj.loglik - fr.loglik) <= 1e-6 * abs(fr.loglik)
    end
    f6 = fit(MN, Y, X; reference=6)
    f1 = fit(MN, Y, X; reference=1)
    @test maximum(abs, f6.clr .- f1.clr) <= 1e-8          # reference invariance
    @test maximum(abs, sum(f6.clr; dims=2)) <= 1e-12      # CLR sums to zero
    @test all(ismissing, f6.clr_q[1, :])                  # intercept not tested
end
