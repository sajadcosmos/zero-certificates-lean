# Claim-by-claim verification map

Each numbered result of the paper is listed with the Lean declarations in `ZeroCertificates.lean` that prove it. All names live in the namespace `ZeroCert`.

The classical bounds `CauchyBound`, `VietaBound` and `RoucheLinear` enter as explicit hypotheses wherever they are used (see the README).

## Section 2 — Certificates

| Paper | Lean |
|---|---|
| Theorem 2.3 (Certificate transfer) | `certificate_transfer` |
| Proposition 2.5 (Vieta lower certificate) | `vieta_lower_certificate` |

## Section 3 — Cauchy-type certificates

| Paper | Lean |
|---|---|
| Theorem 3.1 (Monic Cauchy certificate) | `monic_cauchy_certificate`, `monic_cauchy_radius` |
| Corollary 3.2 (Gaussian monic Cauchy certificate) | `gauss_monic_lower`, `gauss_monic_upper`, `gauss_monic_radius` |
| Theorem 3.3 (Sub-Weibull Cauchy radius) | `subWeibull_cauchy_radius` |
| Corollary 3.4 (Sub-Gaussian radius) | `subGaussian_cauchy_radius` |
| Theorem 3.5 (i)–(iii) (scaled certificates, envelope, Fujiwara-type bound) | `zerosWithin_scaledCauchy`, `zerosWithin_optScaledCauchy`, `optScaledCauchy_le_two_fujiwara` |
| Corollary 3.6 (Fujiwara-type probabilistic certificate) | `fujiwara_certificate`, `gauss_fujiwara_certificate` |
| Proposition 3.7 (implicit Cauchy radius: well-definedness, ordering, optimality) | `implicitCauchy_spec`, `zerosWithin_implicitCauchy`, `cauchy_hierarchy`, `implicitCauchy_isGreatest` |

## Section 4 — Exact common-denominator certificate

| Paper | Lean |
|---|---|
| Theorem 4.1 (distribution and certificate) | `ratio_law`, `ratio_certificate` |
| Corollary 4.2 (Certified confidence radius) | `ratioLaw_properties`, `ratio_radius` |
| Proposition 4.3 (Union-bound form) | `ratio_union_bound`, `ratio_union_radius` |
| Proposition 4.4 (Vieta upper bound, Gaussian case) | `vieta_gauss_upper` |
| Remark 4.5 (`I_1(r) = (2/π) arctan r`, `I_n(1) = 1/(n+1)`) | `ratioLaw_one`, `ratioLaw_at_one` |

## Section 5 — Asymptotics

| Paper | Lean |
|---|---|
| Lemma 5.1 (Gumbel limit with moment convergence) | `gumbel_limit`, `gumbelF_tendsto`, `gumbelTailMean_tendsto`, `integral_gumbelG`, `integral_gumbelG_sq_le`, `maxAbs_div_bn_tendsto` |
| Theorem 5.2, Eq. (5.7) | `ratioLawInv_second_order` |
| Theorem 5.2, Eq. (5.8) | `ratioLawInv_log_expansion` |
| Eq. (5.9): `I_n(r) = E H̄(M_n/r)` | `ratioLaw_eq_integral_hnTail` |
| Eq. (5.11) | `ratioLaw_expansion` |
| Corollary 5.3 | `ratioLawInv_order`, `ratioLaw_ge_indep`, `indepCauchyQuantile_spec`, `indepCauchyQuantile_asymp` |

## Section 6 — Degree-independent certificates

| Paper | Lean |
|---|---|
| Theorem 6.1 (Small-ball transfer) | `smallBall_tail_le_one`, `smallBall_tail_ge_one`, `smallBall_radius_le_one`, `smallBall_radius_ge_one` |
| Corollary 6.2 (Real Gaussian confidence radius) | `gaussian_degree_free_tail`, `gaussian_degree_free_radius` |
| Remark 6.3 (complex Gaussian and monic cases) | `complex_gaussian_radius`, `monic_markov_tail` |
| Eq. (6.6) | `tailD_eq` |
| Theorem 6.4 (Extreme-root tail), incl. uniform form (6.9) | `extreme_root_tail`, `extreme_root_tail_uniform` |
| Corollary 6.5 (High-confidence quantile scale) | `highconfidence_exact`, `highconfidence_certificate`, `highconf_key_ineq` |

## Section 7 — Inner, annular and Chernoff certificates

| Paper | Lean |
|---|---|
| Lemma 7.1 (Reversed Cauchy certificate) | `reversed_cauchy`, `innerRadius_ge_reversed_cauchy` |
| Theorem 7.2 (Gaussian annular certificate) | `gaussian_annular_union`, `gaussian_annular_cot` |
| Proposition 7.3 (Exact-marginal annulus) | `exact_marginal_annulus`, `exact_marginal_annulus_radius`, `degree_free_annulus` |
| Lemma 7.4 (Rouché outer certificate) | `rouche_outer` |
| Theorem 7.5 (Chernoff zero certificate) | `chernoff_certificate` |
| Eq. (7.1) | `chernoffPsi` |
| Corollary 7.6 (Gaussian Rouché–Chernoff certificate) | `gaussian_chernoff_certificate`, `integral_exp_mul_abs_gaussian`, `chernoffPsi_normalization` |
