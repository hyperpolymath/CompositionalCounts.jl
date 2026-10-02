# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    CompositionalCounts

Multinomial (MN) and Dirichlet-Multinomial (DM) regression for compositional
count data. Supported and unsupported conditions for each model are published
in `docs/method-conditions/`; every unsupported condition raises a typed
[`CompositionalError`](@ref) — never a fallback, never an empty result.
"""
module CompositionalCounts

export CompositionalError, InvalidCounts, UnidentifiableTaxon, RankDeficientDesign,
       InvalidReference, NonConvergence, BackendUnavailable,
       UnidentifiableDispersion, BoundaryEstimate, MultipleOptima, SingularInformation,
       validate_counts, validate_design, prevalence, select_reference, validate_reference

include("Errors.jl")
include("Identify.jl")

end # module
