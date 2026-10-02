<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Multinomial (MN) regression: supported and unsupported conditions

**Status:** published before implementation. The code must satisfy this document.
Where the two disagree, the code is wrong.

## Model

For sample *i* = 1…n with count vector **y**ᵢ over taxa *j* = 1…J and total Nᵢ = Σⱼ yᵢⱼ:

    yᵢ ~ Multinomial(Nᵢ, pᵢ),   pᵢⱼ = exp(ηᵢⱼ) / Σₖ exp(ηᵢₖ),   ηᵢⱼ = xᵢᵀ βⱼ,   β_ref = 0.

- **X** is the n × p design matrix. Include an intercept column if you want one; the package does not add it.
- *ref* is the reference taxon.
- **Totals are conditioned on, not modelled.** Nᵢ is not an offset. A sequencing-depth covariate such as log Nᵢ may be placed in **X** by the user, as in the `MGLM` documentation example, but it is never added implicitly.

This is the baseline-category logit model fitted by `MGLM::MGLMreg(dist = "MN")` (Zhang et al. 2017). `MGLM` uses the last category as its reference. The package uses a validated reference taxon (below). The two parameterisations are related by an invertible linear map (`proofs/`, theorem *reference change*).

## Reported quantities

| Quantity | Definition | Reference-dependent? |
|---|---|---|
| Log-ratio coefficients β̂ⱼ | log(pⱼ / p_ref) slope, j ≠ ref | yes |
| Centred (CLR) effects γ̂ⱼ | β̂ⱼ − (1/J) Σₖ β̂ₖ, with β̂_ref = 0 | **no**; Σⱼ γ̂ⱼ = 0 exactly |
| Standard errors | inverse observed information (equal to the expected information for this canonical-link model); delta method for γ̂ | as above |
| Wald z and p | two-sided, per coefficient | as above |
| BH q-values | Benjamini–Hochberg within each covariate, across the J CLR effects | no |
| Provenance | backend, package/R/`MGLM` versions, reference taxon, penalty, convergence report | n/a |

The primary hypothesis tests are on the CLR effects, because these do not depend on the choice of reference. The BH step is applied once per covariate, across taxa. The intercept is not tested.

**Caveat, stated rather than hidden.** CLR effects are linearly dependent (they sum to zero), so their test statistics are correlated. BH controls FDR under independence or positive regression dependence (PRDS), and PRDS is not established for CLR contrasts. The package reports BH q-values and states this caveat in the provenance block. Benjamini–Yekutieli is available on request as the dependence-robust alternative.

## Supported conditions

1. **Counts:** non-negative integers. Nᵢ ≥ 1 for every sample.
2. **Design:** **X** has full column rank p, and n > p.
3. **Taxa:** J ≥ 2, and every taxon has a positive total count across samples.
4. **Reference taxon:** prevalence (the fraction of samples with yᵢ,ref > 0) is ≥ 0.5, and the total count is > 0.
   - **Default selection** is deterministic: maximum prevalence, then maximum total count, then lowest column index.
   - **A user-supplied reference** is checked against the same rule and refused if it fails. It is never silently replaced.
5. **Penalty:** a Songbird-style L1 penalty λ ≥ 0 on the non-intercept coefficients is supported for *estimation*. When λ > 0, standard errors, p-values and q-values are **not computed**, and the fit says so with an explicit status. A penalised estimate does not support Wald inference, and an empty column would read as "not significant".

## Unsupported conditions: the fit refuses with a typed error

Refusals are errors, never fallbacks. There is no substitution of another method, backend or reference, and no empty result.

| Condition | Error |
|---|---|
| Negative, non-integer or non-finite count | `InvalidCounts` |
| A sample with Nᵢ = 0 | `InvalidCounts` |
| A taxon with zero total count (its MLE is −∞) | `UnidentifiableTaxon` |
| Rank-deficient **X**, or n ≤ p | `RankDeficientDesign` |
| Reference taxon fails rule 4 | `InvalidReference` |
| Optimiser did not converge within its iteration and gradient tolerances | `NonConvergence` (carries the report) |
| Coefficients diverge, e.g. quasi-complete separation by a covariate | `NonConvergence` (divergence) |
| `backend = :r` without RCall, R or `MGLM` | `BackendUnavailable` |

## Validation: the acceptance tests

1. **Against R `MGLM` 0.2.3**, pinned in `renv.lock`, on three fixtures of about 100 taxa: a mock community, a gut subset and a soil subset. Each fixture's source and licence is recorded in `test/fixtures/README.md`.
   - **Comparison:** MGLM's last-category coefficients are mapped to the package's reference through the reference-change map.
   - **Tolerances:** coefficients and SEs agree within **1e-3** absolute; maximised log-likelihoods agree within 1e-6 relative.
   - A fixture on which `MGLM` itself reports non-convergence is invalid as a reference and is not used.
2. **Planted truth.** Simulate from known β with an `n`, `J` and `N` stated in the test. The true value must lie within 3 SE of the estimate for at least 95 % of coefficients, over a fixed seed set.
3. **Gradient check.** The analytic gradient Xᵀ(Y − N ∘ P) matches central finite differences. A deliberately wrong gradient must fail this test (positive control).
4. **Refusal tests:** one test per row of the refusal table, each asserting the typed error.

## What is proved, and what is only tested

This is the authoritative split; it is mirrored in `proofs/PROOF-STATUS.md`.

**Proved (Agda, `--safe --without-K`):**
- reference change is a bijection on coefficients and leaves fitted probabilities invariant;
- CLR effects sum to zero;
- softmax is shift-invariant;
- BH monotonicity and step-up correctness;
- the reference-taxon predicate is decidable, and the fit refuses exactly when it fails.

**Tested, not proved:**
- convexity in practice;
- optimiser convergence;
- floating-point stability;
- runtime.

## Not claimed

Taxon proportions are compositional. A positive CLR effect means that a taxon rises *relative to the geometric mean of the community*, not that its absolute abundance rises (Morton et al. 2019; Gloor et al. 2017).

## References

- Aitchison, J. (1986). *The Statistical Analysis of Compositional Data.* Chapman & Hall.
- Benjamini, Y. & Hochberg, Y. (1995). Controlling the false discovery rate. *JRSS-B* 57, 289–300.
- Benjamini, Y. & Yekutieli, D. (2001). The control of the false discovery rate in multiple testing under dependency. *Ann. Statist.* 29, 1165–1188.
- Gloor, G. B. et al. (2017). Microbiome datasets are compositional: and this is not optional. *Front. Microbiol.* 8, 2224.
- Morton, J. T. et al. (2019). Establishing microbial composition measurement standards with reference frames. *Nat. Commun.* 10, 2719.
- Zhang, Y., Zhou, H., Zhou, J. & Sun, W. (2017). Regression models for multivariate count data. *J. Comput. Graph. Statist.* 26, 1–13.
