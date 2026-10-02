# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

using LinearAlgebra: I as Id, kron, diag, cholesky, Symmetric, isposdef
using SpecialFunctions: erfc

"""
    bh_adjust(p::AbstractVector{<:Real}) -> Vector{Float64}

Benjamini–Hochberg step-up adjusted p-values (q-values): q₍ᵢ₎ = min over k ≥ i of
p₍ₖ₎·m/k, capped at 1, returned in the input order.
"""
function bh_adjust(p::AbstractVector{<:Real})
    m = length(p)
    m == 0 && return Float64[]
    all(x -> 0 <= x <= 1, p) || throw(ArgumentError("p-values must lie in [0, 1]"))
    o = sortperm(p)
    q = Vector{Float64}(undef, m)
    running = 1.0
    for i in m:-1:1
        running = min(running, p[o[i]] * m / i)
        q[o[i]] = running
    end
    return q
end

"""
    wald_p(est, se)

Two-sided normal-approximation Wald p-value for estimate `est` with standard error `se`.
"""
wald_p(est::Real, se::Real) = erfc(abs(est / se) / sqrt(2))

"""
    centring_matrix(J)

The J × J centring matrix C = I − 11ᵀ/J; `B * C` maps coefficients to CLR effects.
"""
centring_matrix(J::Integer) = Matrix{Float64}(Id, J, J) .- 1.0 / J

"""
    inference(B, M, info, tested; free_cols) -> NamedTuple

Standard errors, CLR effects, Wald p and BH q from coefficients `B` (p × J), the
linear map `M` with vec(B) = M θ, the observed information `info` for θ, and the
`tested` covariate mask. Columns not in `free_cols` get `missing` SEs. Throws
[`SingularInformation`](@ref) when `info` is not positive definite.
"""
function inference(B::Matrix{Float64}, M::AbstractMatrix, info::AbstractMatrix,
                   tested::AbstractVector{Bool}; free_cols)
    p, J = size(B)
    S = Symmetric((info + info') / 2)
    isposdef(S) || throw(SingularInformation(
        "observed information is not positive definite at the optimum"))
    Σ = inv(cholesky(S))
    covB = M * Σ * M'
    se = Matrix{Union{Missing,Float64}}(missing, p, J)
    dB = reshape(sqrt.(max.(diag(covB), 0.0)), p, J)
    for j in free_cols, r in 1:p
        se[r, j] = dB[r, j]
    end
    C = centring_matrix(J)
    Γ = B * C
    L = kron(C, Matrix{Float64}(Id, p, p))    # vec(B C) = (Cᵀ ⊗ I) vec(B), C symmetric
    dΓ = reshape(sqrt.(max.(diag(L * covB * L'), 0.0)), p, J)
    clr_se = Matrix{Union{Missing,Float64}}(missing, p, J)
    clr_p = Matrix{Union{Missing,Float64}}(missing, p, J)
    clr_q = Matrix{Union{Missing,Float64}}(missing, p, J)
    for r in 1:p
        clr_se[r, :] .= dΓ[r, :]
        tested[r] || continue
        pr = [wald_p(Γ[r, j], dΓ[r, j]) for j in 1:J]
        clr_p[r, :] .= pr
        clr_q[r, :] .= bh_adjust(pr)
    end
    return (se=se, clr=Γ, clr_se=clr_se, clr_p=clr_p, clr_q=clr_q)
end

"""
    no_inference(B)

The inference fields for a penalised fit: CLR point estimates only, every
uncertainty field `missing` (explicitly not computed, never "not significant").
"""
function no_inference(B::Matrix{Float64})
    p, J = size(B)
    miss() = Matrix{Union{Missing,Float64}}(missing, p, J)
    return (se=miss(), clr=B * centring_matrix(J), clr_se=miss(), clr_p=miss(), clr_q=miss())
end

const BH_CAVEAT = "BH q-values assume independence or PRDS among the J CLR tests " *
                  "of a covariate; CLR effects sum to zero, so PRDS is not established"
