# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    provenance(backend, model; reference, penalty, convergence,
               versions=NamedTuple(), caveats=()) -> NamedTuple

The provenance record every [`CompositionalFit`](@ref) carries: backend, model,
package and Julia versions, any backend-specific `versions` (e.g. MGLM and R),
reference taxon, penalty, the solver's convergence report, and caveats. The
Benjamini–Hochberg dependence caveat is always first.
"""
function provenance(backend::Symbol, model::AbstractString; reference::Int, penalty::Real,
                    convergence::NamedTuple, versions::NamedTuple=NamedTuple(),
                    caveats::Tuple=())
    core = (backend=backend, model=String(model),
            package_version=string(pkgversion(@__MODULE__)), julia_version=string(VERSION))
    return merge(core, versions,
                 (reference=reference, penalty=Float64(penalty), convergence=convergence,
                  caveats=(BH_CAVEAT, caveats...)))
end
