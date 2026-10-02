# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    CompositionalModel

Abstract supertype of the model tags [`MN`](@ref) and [`DM`](@ref) passed to [`fit`](@ref).
"""
abstract type CompositionalModel end

"""
    MN

Multinomial baseline-category logit regression (`docs/method-conditions/multinomial.md`).
"""
struct MN <: CompositionalModel end

"""
    DM

Dirichlet-Multinomial regression, α_j = exp(Xβ_j)
(`docs/method-conditions/dirichlet-multinomial.md`).
"""
struct DM <: CompositionalModel end

"""
    CompositionalFit

Result of [`fit`](@ref). Fields:

- `model`        — `MN` or `DM`
- `coef`         — p × J coefficients. For MN the reference column is exactly 0.
- `se`           — p × J standard errors (`missing` for the MN reference column, and
                   everywhere when `status == :penalised_no_inference`)
- `clr`, `clr_se`, `clr_p`, `clr_q` — p × J centred effects and their Wald p and
                   BH q (within covariate, across taxa); `missing` for untested rows
                   (constant/intercept columns) and for penalised fits
- `tested`       — length-p vector: which covariates were tested
- `loglik`       — maximised log-likelihood including the multinomial constant
- `reference`    — reference taxon index
- `status`       — `:inference` or `:penalised_no_inference`
- `extra`        — model-specific quantities (DM: fitted α₊ and ρ per sample)
- `provenance`   — backend, versions, penalty, convergence report, caveats
"""
struct CompositionalFit
    model::Type{<:CompositionalModel}
    coef::Matrix{Float64}
    se::Matrix{Union{Missing,Float64}}
    clr::Matrix{Float64}
    clr_se::Matrix{Union{Missing,Float64}}
    clr_p::Matrix{Union{Missing,Float64}}
    clr_q::Matrix{Union{Missing,Float64}}
    tested::Vector{Bool}
    loglik::Float64
    reference::Int
    status::Symbol
    extra::NamedTuple
    provenance::NamedTuple
end

"""
    fit(model, Y, X; reference=nothing, penalty=0.0, backend=:julia) -> CompositionalFit

Fit `model` (`MN` or `DM`) to counts `Y` (n samples × J taxa) with design `X`
(n × p; include an intercept column yourself). `reference` is a taxon index or
`nothing` for the deterministic default; `penalty` is the L1 weight λ ≥ 0 on
non-constant columns (λ > 0 disables inference); `backend` is `:julia` or `:r`
(requires `using RCall` and R package `MGLM`). Every unsupported condition throws
a [`CompositionalError`](@ref); there is no fallback.
"""
function fit(::Type{M}, Y::AbstractMatrix, X::AbstractMatrix;
             reference::Union{Nothing,Integer}=nothing, penalty::Real=0.0,
             backend::Symbol=:julia) where {M<:CompositionalModel}
    validate_counts(Y)
    validate_design(X, size(Y, 1))
    ref = reference === nothing ? select_reference(Y) : validate_reference(Y, reference)
    (isfinite(penalty) && penalty >= 0) ||
        throw(ArgumentError("penalty must be finite and ≥ 0, got $penalty"))
    Yf = Matrix{Float64}(Y)
    Xf = Matrix{Float64}(X)
    if backend === :julia
        return _fit_julia(M, Yf, Xf, ref, Float64(penalty))
    elseif backend === :r
        penalty == 0 || throw(ArgumentError(
            "backend = :r supports penalty = 0 only; MGLMsparsereg is not wired"))
        return _fit_r(M, Yf, Xf, ref)
    else
        throw(ArgumentError("backend must be :julia or :r, got :$backend"))
    end
end

"""
    _fit_r(model, Y, X, ref)

R `MGLM` backend. Its methods live in the `CompositionalCountsRCallExt`
extension; without `using RCall` this fallback method throws
[`BackendUnavailable`](@ref) rather than switching backend.
"""
_fit_r(::Type{<:CompositionalModel}, Y, X, ref) = throw(BackendUnavailable(
    "backend = :r needs `using RCall` and the R package MGLM (pinned in renv.lock)"))

"""
    constant_columns(X) -> Vector{Bool}

Columns of `X` whose entries are all equal (intercepts). They are neither
penalised nor tested.
"""
constant_columns(X::AbstractMatrix) = [all(==(X[1, r]), @view X[:, r]) for r in axes(X, 2)]
