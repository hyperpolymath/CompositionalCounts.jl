<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# CompositionalCounts.jl

Multinomial (MN) and Dirichlet-Multinomial (DM) regression for compositional
count data such as microbiome taxon tables.

**Status: 0.1.0-DEV — not yet usable.** Input validation and the reference-taxon rule are
implemented and tested; the model fits are not. Each model's supported and
unsupported conditions are published *before* implementation:

- [`docs/method-conditions/multinomial.md`](docs/method-conditions/multinomial.md)
- [`docs/method-conditions/dirichlet-multinomial.md`](docs/method-conditions/dirichlet-multinomial.md)

## Design commitments

- **One API, two backends.** A pure-Julia solver and R [`MGLM`](https://cran.r-project.org/package=MGLM)
  via RCall (package extension). Each is tested against the other; neither is a
  fallback for the other.
- **Refuse, never substitute.** Every unsupported condition raises a typed
  `CompositionalError`. No silent change of method, backend or reference taxon,
  and no empty result standing in for a negative one.
- **Proved vs tested, stated per claim.** Algebraic properties (reference-change
  invariance, centred effects summing to zero, softmax shift invariance,
  Benjamini–Hochberg) are machine-checked in Agda; numerical behaviour is tested
  against `MGLM` and planted-truth simulations. See the method-conditions docs.

## Licence

Code: MPL-2.0 (`LICENSE`). Documentation: CC-BY-SA-4.0. Each file carries its
SPDX identifier.
