# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    CompositionalCountsRCallExt

R backend: fits through `MGLM::MGLMreg.fit` (MGLM pinned in the package's
`renv.lock`). Loaded automatically by `using RCall`.
"""
module CompositionalCountsRCallExt

using CompositionalCounts
using CompositionalCounts: MN, DM, CompositionalFit, BackendUnavailable, NonConvergence,
      inference, constant_columns, mn_derivs, mn_embedding, multinomial_constant,
      check_divergence, provenance
using RCall

"""
    mglm_version() -> String

Version of the R package MGLM visible to RCall; throws `BackendUnavailable` if absent.
"""
function mglm_version()
    ok = rcopy(Bool, R"requireNamespace('MGLM', quietly = TRUE)")
    ok || throw(BackendUnavailable(
        "R package MGLM is not installed in R's library paths (see renv.lock)"))
    return rcopy(String, R"as.character(utils::packageVersion('MGLM'))")
end

"""
    mglm_fit(Y, X, dist) -> (coef, se, logL, iter, maxgrad)

Call `MGLM::MGLMreg.fit` and return its coefficients, SEs, log-likelihood,
iteration count and max |gradient|.
"""
function mglm_fit(Y::Matrix{Float64}, X::Matrix{Float64}, dist::String)
    r = R"""
        f <- MGLM::MGLMreg.fit(Y = $Y, X = $X, dist = $dist)
        list(coef = unname(as.matrix(f@coefficients)), se = unname(as.matrix(f@SE)),
             logL = f@logL, iter = f@iter, grad = max(abs(f@gradient)))
    """
    d = rcopy(r)
    return Matrix{Float64}(d[:coef]), Matrix{Float64}(d[:se]), Float64(d[:logL]),
           Int(d[:iter]), Float64(d[:grad])
end

const MGLM_MAXITERS = 150   # MGLMreg.fit default

"""
    _fit_r(::Type{MN}, Y, X, ref) -> CompositionalFit

MN via MGLM: columns are permuted so `ref` is last (MGLM's reference), and the
estimates are mapped back. SEs are MGLM's; CLR inference uses the package's
information matrix evaluated at MGLM's estimate (recorded in provenance).
"""
function CompositionalCounts._fit_r(::Type{MN}, Y::Matrix{Float64}, X::Matrix{Float64}, ref::Int)
    ver = mglm_version()
    n, J = size(Y)
    p = size(X, 2)
    free = [j for j in 1:J if j != ref]
    coef, se, logL, iter, maxgrad = mglm_fit(Y[:, vcat(free, ref)], X, "MN")
    iter >= MGLM_MAXITERS && throw(NonConvergence(
        "MGLM MN hit its iteration cap ($iter); not reporting its estimate"))
    B = zeros(p, J)
    B[:, free] .= coef
    check_divergence(B, Y, X)
    _, _, Imat = mn_derivs(B, Y, X, free)
    tested = collect(.!constant_columns(X))
    inf = inference(B, mn_embedding(p, J, free), Imat, tested; free_cols=free)
    se_full = Matrix{Union{Missing,Float64}}(missing, p, J)
    se_full[:, free] .= se
    prov = provenance(:r, "MN"; reference=ref, penalty=0.0,
                      versions=(mglm_version=ver, r_version=rcopy(String, R"R.version.string")),
                      convergence=(converged=true, iterations=iter, max_abs_gradient=maxgrad,
                                   solver="MGLM::MGLMreg.fit"),
                      caveats=("CLR SEs use the package's information at MGLM's estimate",))
    return CompositionalFit(MN, B, se_full, inf.clr, inf.clr_se, inf.clr_p, inf.clr_q,
                            tested, logL, ref, :inference, NamedTuple(), prov)
end

end # module
