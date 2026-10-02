<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Dirichlet-Multinomial (DM) regression: supported and unsupported conditions

**Status:** published before implementation. The code must satisfy this document.
Where the two disagree, the code is wrong.
Shared definitions (counts, design, reference rule, BH, refusal policy) are in [`multinomial.md`](multinomial.md). Only the differences are stated here.

## Model

    yᵢ ~ DirMult(Nᵢ, αᵢ),   αᵢⱼ = exp(xᵢᵀ βⱼ),   j = 1…J   (no reference category).

For each sample, write α₊ᵢ = Σⱼ αᵢⱼ and pᵢⱼ = αᵢⱼ / α₊ᵢ. Then:

- the mean is E yᵢⱼ = Nᵢ pᵢⱼ;
- the variance is Var yᵢⱼ = Nᵢ pᵢⱼ(1 − pᵢⱼ)·(Nᵢ + α₊ᵢ)/(1 + α₊ᵢ);
- the intra-class correlation is ρᵢ = 1/(1 + α₊ᵢ).

As α₊ᵢ → ∞, the DM reduces to the multinomial.

This is the model fitted by `MGLM::MGLMreg(dist = "DM")` (Zhang et al. 2017). The package uses **the same parameterisation**, so its estimates are compared with `MGLM` directly, coefficient by coefficient. It is not a model with a separate scalar dispersion. Overdispersion is carried by the scale of α, and covariates can move it. It is also not a logistic-normal model with a full covariance matrix; the DM covariance is fixed by α.

All J coefficient vectors are identified, because the common scale of α carries the overdispersion. This holds only when some samples have Nᵢ ≥ 2; see refusals.

## Reported quantities

| Quantity | Definition |
|---|---|
| Coefficients β̂ⱼ, j = 1…J | log αⱼ slopes, directly comparable with `MGLM` |
| Log-ratio contrasts β̂ⱼ − β̂_ref | slope of log(pⱼ / p_ref), the mean-proportion log-ratio; reference rule as in MN |
| Centred (CLR) effects γ̂ⱼ = β̂ⱼ − (1/J) Σₖ β̂ₖ | reference-invariant; Σⱼ γ̂ⱼ = 0 exactly |
| Fitted α₊ᵢ and ρᵢ per sample | overdispersion, reported rather than summarised away |
| SEs | inverse observed information (the negative Hessian of the log-likelihood); delta method for the contrasts |
| Wald p, BH q | as in MN: CLR effects, BH within covariate across taxa, same dependence caveat |
| Multistart report | number of starts, seeds, log-likelihood of each start, best-vs-runner-up spread |

## Estimation

- **Method:** maximum likelihood on the log-gamma form of the DM likelihood.
- **Starting values:** method-of-moments estimates of p and ρ give the first start. Further starts perturb it with recorded seeds; the default is 8 starts.
- **Optimum:** the reported optimum is the best log-likelihood across starts.
- **Optimiser:** the DM likelihood is not concave in β, so a single start is never trusted.

## Supported conditions

These are the MN conditions 1–5, plus:

6. **Nᵢ ≥ 2 for at least p samples.** With Nᵢ = 1 the DM reduces to a categorical draw, and the scale of α is not identified.
7. **Overdispersion is detectable.** The fit must be away from the multinomial boundary, as the next section defines.

## Unsupported conditions: the fit refuses with a typed error

These are all MN refusals, plus:

| Condition | Error |
|---|---|
| Fewer than p samples with Nᵢ ≥ 2 | `UnidentifiableDispersion` |
| **Multinomial boundary:** the likelihood still increases along the common-scale direction (every intercept + c) at termination, with max α₊ᵢ > 1e6 | `BoundaryEstimate`, with the advice "no detectable overdispersion — fit MN" |
| Two starts reach log-likelihoods within 1e-6 relative of each other but have coefficients more than 1e-3 apart | `MultipleOptima` (carries both solutions) |
| Observed information is not positive definite at the optimum | `SingularInformation` |

The 1e6 threshold is a documented convention, not a theorem. Two tests calibrate it:

- data simulated from a true multinomial **must** raise `BoundaryEstimate`;
- data simulated from a DM with ρ = 0.05 **must not** raise it.

## Validation: the acceptance tests

1. **Against R `MGLM` 0.2.3** on the three MN fixtures.
   - Coefficients and SEs agree within **1e-3** absolute, with no reparameterisation needed.
   - Maximised log-likelihoods agree within 1e-6 relative.
   - If the package finds a strictly higher log-likelihood than `MGLM`, that is reported as a finding, not tuned away.
2. **Planted truth.** Simulate from a DM with known β at ρ ∈ {0.01, 0.05, 0.2}, with the `n`, `J` and `N` stated in the test. The 3-SE coverage criterion is as in MN.
3. **Multistart.** A fixture known to have a second local optimum must either report the global one or raise `MultipleOptima`. It must never silently report the worse one.
4. **The boundary tests** described above.
5. **Gradient check** against central finite differences, with a planted wrong-gradient positive control.

## What is proved, and what is only tested

**Proved:** the algebraic statements for the *contrasts*:

- reference change on β̂ⱼ − β̂_ref;
- CLR effects summing to zero;
- shift invariance of p under βⱼ ↦ βⱼ + c for all j. This is the fact that makes the common scale a separate, overdispersion direction.

These are the same theorems as for MN, applied to the derived contrasts.

**Tested, not proved:**

- that the DM likelihood is non-concave and can have local optima;
- convergence and the multistart behaviour;
- the DM → MN limit as α₊ → ∞;
- the boundary threshold;
- floating-point stability;
- runtime.

## References

Shared references are in [`multinomial.md`](multinomial.md). In addition:

- La Rosa, P. S. et al. (2012). Hypothesis testing and power calculations for taxonomic-based human microbiome data. *PLoS ONE* 7, e52078.
- Mosimann, J. E. (1962). On the compound multinomial distribution, the multivariate β-distribution, and correlations among proportions. *Biometrika* 49, 65–82.
