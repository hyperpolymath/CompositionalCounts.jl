# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

using LinearAlgebra: rank

"""
    validate_counts(Y::AbstractMatrix)

Check that `Y` (n samples × J taxa) holds finite non-negative integer counts,
that every sample total is ≥ 1, that J ≥ 2, and that every taxon has a positive
total. Throws [`InvalidCounts`](@ref) or [`UnidentifiableTaxon`](@ref); returns
`nothing` on success.
"""
function validate_counts(Y::AbstractMatrix)
    n, J = size(Y)
    J >= 2 || throw(InvalidCounts("need at least 2 taxa, got $J"))
    n >= 1 || throw(InvalidCounts("no samples"))
    for (k, y) in pairs(Y)
        (isfinite(y) && y >= 0 && isinteger(y)) ||
            throw(InvalidCounts("entry $(Tuple(k)) = $y is not a finite non-negative integer"))
    end
    for i in 1:n
        sum(@view Y[i, :]) >= 1 || throw(InvalidCounts("sample $i has total count 0"))
    end
    for j in 1:J
        sum(@view Y[:, j]) > 0 ||
            throw(UnidentifiableTaxon("taxon $j has zero total count; its MLE is -Inf"))
    end
    return nothing
end

"""
    validate_design(X::AbstractMatrix, n::Integer)

Check that the design `X` has `n` rows, full column rank p, and n > p. Throws
[`RankDeficientDesign`](@ref); returns `nothing` on success.
"""
function validate_design(X::AbstractMatrix, n::Integer)
    size(X, 1) == n || throw(RankDeficientDesign("X has $(size(X, 1)) rows, counts have $n"))
    all(isfinite, X) || throw(RankDeficientDesign("X has non-finite entries"))
    p = size(X, 2)
    n > p || throw(RankDeficientDesign("need n > p, got n = $n, p = $p"))
    rank(Matrix{Float64}(X)) == p || throw(RankDeficientDesign("X is rank deficient (rank < $p)"))
    return nothing
end

"""
    prevalence(Y::AbstractMatrix, j::Integer)

Fraction of samples (rows of `Y`) in which taxon `j` has a positive count.
"""
prevalence(Y::AbstractMatrix, j::Integer) = count(>(0), @view Y[:, j]) / size(Y, 1)

"""
    reference_ok(Y, j) -> Bool

The reference-taxon predicate of `docs/method-conditions/multinomial.md` rule 4:
prevalence ≥ 0.5 and positive total count.
"""
reference_ok(Y::AbstractMatrix, j::Integer) =
    1 <= j <= size(Y, 2) && prevalence(Y, j) >= 0.5 && sum(@view Y[:, j]) > 0

"""
    validate_reference(Y::AbstractMatrix, j::Integer)

Refuse a user-supplied reference taxon `j` that fails rule 4 by throwing
[`InvalidReference`](@ref). Never substitutes another taxon. Returns `j`.
"""
function validate_reference(Y::AbstractMatrix, j::Integer)
    1 <= j <= size(Y, 2) || throw(InvalidReference("taxon index $j out of 1:$(size(Y, 2))"))
    reference_ok(Y, j) || throw(InvalidReference(
        "taxon $j has prevalence $(prevalence(Y, j)) (< 0.5) or zero total; choose another reference"))
    return j
end

"""
    select_reference(Y::AbstractMatrix) -> Int

Deterministic default reference: maximum prevalence, then maximum total count,
then lowest column index. Throws [`InvalidReference`](@ref) when no taxon
satisfies rule 4.
"""
function select_reference(Y::AbstractMatrix)
    J = size(Y, 2)
    key(j) = (prevalence(Y, j), sum(@view Y[:, j]), -j)
    best = argmax(key, 1:J)
    return validate_reference(Y, best)
end
