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
  - p comes from the MN fit, with its coefficients centred across taxa so that the start, and hence the whole DM fit, does not depend on the reference.
  - ρ̂ comes from the Pearson statistic, clamped to [1e-4, 0.5].
  - Start k ≥ 1 adds `Xoshiro(k)` normal noise of 0.5 per standardised design column and 0.5 per taxon level. Seed 0 is the moment start.
- **Optimum:** the reported optimum is the best log-likelihood across starts.
- **Optimiser:** the DM likelihood is not concave in β, so a single start is never trusted.

## Supported conditions

These are the MN conditions 1–5, plus:

6. **Nᵢ ≥ 2 for at least p samples.** With Nᵢ = 1 the DM reduces to a categorical draw, and the scale of α is not identified.
7. **Overdispersion is detectable.** The fit must be away from the multinomial boundary, as the next section defines.
8. **The constant vector lies in the column space of X** (in practice, the design has an intercept). Only then is "every α scaled by eᶜ" a direction of the model, and that direction carries the overdispersion. *(Added 2026-10-02 with the implementation; see Amendments.)*

## Unsupported conditions: the fit refuses with a typed error

These are all MN refusals, plus:

| Condition | Error |
|---|---|
| Fewer than p samples with Nᵢ ≥ 2 | `UnidentifiableDispersion` |
| The constant vector is not in the column space of X | `UnidentifiableDispersion` |
| **Multinomial boundary:** the likelihood still increases along the common-scale direction (every intercept + c) at termination, with max α₊ᵢ > 1e6; **or** the iterate runs past max α₊ᵢ > 1e10, where the slope is below floating-point resolution and no slope condition is applied | `BoundaryEstimate`, with the advice "no detectable overdispersion — fit MN" |
| Two starts reach log-likelihoods within 1e-6 relative of each other but some coefficient differs by more than **0.01 of its standard error** at the best start | `MultipleOptima` (carries both solutions). The check is skipped when that information is singular, so that `SingularInformation` is raised instead |
| Observed information is not positive definite at the optimum | `SingularInformation` |

The 1e6 threshold is a documented convention, not a theorem. Two tests calibrate it. Both use n = 200, Nᵢ uniform on 400–600, J = 5, p = 3 and seeds 1–40:

- data simulated from a true multinomial raises `BoundaryEstimate` in **35 of 40** seeds, and the test requires at least 32. The other 5 seeds give finite fits at α₊ between 1.3e4 and 5.2e5.
  - A finite DM MLE on multinomial data is a genuine outcome.
  - No point threshold on α₊ can refuse every such fit without also tuning to the seeds.
- data simulated from a DM with ρ = 0.05 (α₊ ≈ 25–60) raises it in **0 of 40** seeds.

## Validation: the acceptance tests

1. **Against R `MGLM` 0.2.3** on the three MN fixtures. *(Currently one fixture, MGLM's `rnaseq`; the other two are owed, as for MN.)*
   - Coefficients and SEs agree within **1e-3** absolute, with no reparameterisation needed.
   - Maximised log-likelihoods agree within 1e-6 relative.
   - If the package finds a strictly higher log-likelihood than `MGLM`, that is reported as a finding, not tuned away.
2. **Planted truth.** Simulate from a DM with known β at ρ ∈ {0.01, 0.05, 0.2}, with the `n`, `J` and `N` stated in the test. The 3-SE coverage criterion is as in MN.
3. **Multistart.** A fixture known to have a second local optimum must either report the global one or raise `MultipleOptima`. It must never silently report the worse one.
   - No genuine two-optimum fixture has been found yet. Over 80 simulated datasets, every converged start reached the same optimum to within 4.3e-4 SE.
   - The selection rule is therefore unit-tested with hand-made start results:
     - tied optima at different coefficients;
     - jitter below the tolerance;
     - singular information;
     - the status of the best start.
4. **The boundary tests** described above.
5. **Gradient check** against central finite differences, with a planted wrong-gradient positive control. The observed information is also checked against the finite-difference Jacobian of the gradient.
6. **DM → MN limit:** along the common scale, the DM log-likelihood converges to the MN log-likelihood.

## Known limitations

- **Boundary detection** uses one direction, the common scale of α.
  - With group covariates, each group's α₊ can approach the boundary separately.
  - The hard stop at α₊ > 1e10 is the backstop.
  - A detectability criterion would replace the point threshold: for example, a one-sided likelihood-ratio test of DM against its MN limit. That is a candidate for a later version.

## Amendments

**2026-10-02, with the first implementation (I4).** The following changes were measured while the method was being implemented.

- **Condition 8 and its refusal are added.** A design without the constant vector has no common-scale direction.
- **The `MultipleOptima` coefficient distance changes** from 1e-3 absolute to 0.01 standard errors.
  - Measured problem: on multinomial-like data, starts that are equal in log-likelihood to 1e-13 relative differed by 0.002 absolute. That is 1.5e-4 SE, along a direction whose SE was 12.6.
  - An absolute threshold refused a single optimum. A distance in SE units is scale-invariant.
  - The worst jitter measured over 80 datasets was 4.3e-4 SE, below the 0.01 SE threshold by a factor of 24.
- **A hard boundary stop at α₊ > 1e10 is added.** Without it, one start ran to α₊ ≈ 1e18. At that scale the slope's sign is floating-point noise, and the start ended in `NonConvergence`.
- **The calibration "true MN must fire" is restated as the measured rate**, for the reasons given above.

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
