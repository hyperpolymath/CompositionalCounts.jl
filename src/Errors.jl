# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    CompositionalError

Abstract supertype of every refusal the package raises. Each concrete subtype
corresponds to one row of a refusal table in `docs/method-conditions/`.
"""
abstract type CompositionalError <: Exception end

for T in (:InvalidCounts, :UnidentifiableTaxon, :RankDeficientDesign, :InvalidReference,
          :NonConvergence, :BackendUnavailable, :UnidentifiableDispersion,
          :BoundaryEstimate, :SingularInformation)
    @eval begin
        @doc """
            $($(string(T)))(msg)

        Refusal raised for the `$($(string(T)))` condition in `docs/method-conditions/`.
        """
        struct $T <: CompositionalError
            msg::String
        end
        Base.showerror(io::IO, e::$T) = print(io, $(string(T)), ": ", e.msg)
    end
end

"""
    MultipleOptima(msg, loglik, coef)

Refusal raised when two DM starts reach the same log-likelihood (within the
documented tolerance) at materially different coefficients. Carries both
solutions: `loglik` and `coef` are 2-tuples (best first).
"""
struct MultipleOptima <: CompositionalError
    msg::String
    loglik::NTuple{2,Float64}
    coef::NTuple{2,Matrix{Float64}}
end
Base.showerror(io::IO, e::MultipleOptima) = print(io, "MultipleOptima: ", e.msg)
