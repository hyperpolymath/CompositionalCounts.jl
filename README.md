<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# CompositionalCounts.jl

Multinomial (MN) and Dirichlet-Multinomial (DM) regression for compositional
count data such as microbiome taxon tables.

**Status: 0.1.0-DEV.** What exists today:

| Component | State |
|---|---|
| Input validation, reference-taxon rule | implemented, tested |
| MN fit (Julia Newton; L1 via FISTA, no inference) | implemented, tested (gradient check, planted truth, refusals) |
| MN via R `MGLM` 0.2.3 (RCall extension) | implemented; CI job agrees with the Julia fit to 1e-3 |
| DM fit | planned |
| Agda proofs of the algebraic claims | planned |

Each model's supported and unsupported conditions are published *before*
implementation:

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
  Benjamini–Hochberg) are to be machine-checked in Agda (planned, not yet in
  this repository); numerical behaviour is tested against `MGLM` and
  planted-truth simulations. See the method-conditions docs.

## Licence

Code: MPL-2.0 (`LICENSE`). Documentation: CC-BY-SA-4.0. Each file carries its
SPDX identifier.

## Applications in practice

The target use is differential-abundance modelling of count compositions
where per-taxon negative-binomial fits are unstable: low-count taxa, small
studies, and designs where the counts are a composition by construction.
Proposed to MetaManifold as
[issue #22](https://github.com/JoshuaJewell/MetaManifold-WebUI/issues/22):
multinomial and Dirichlet-multinomial regression neither require nor add a
pseudocount (the composition is the model), and the centred effects sum to
zero across taxa. What that buys is the model's own arithmetic: no zeros
are filled in on the way to the fit. It is not a claim about the input --
`fit` takes the caller's counts as given (finite, non-negative integers,
each sample non-empty), so a table that was zero-filled upstream is modelled
as the counts it now is. The guarantee is about what the model does not do,
not about what a caller cannot have done beforehand.
The practical value for a working analyst: the question a reviewer asks --
"did the low-count taxa drive that call?" -- has a modelling answer rather
than a filtering heuristic.
