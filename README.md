# Lean 4 formalization: *Finite-Degree Probabilistic Zero Certificates for Random Polynomials*

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23523458.svg)](https://doi.org/10.5281/zenodo.23523458)

This repository contains the complete Lean 4 / Mathlib formalization accompanying

> S. A. Sheikh,
> *Finite-Degree Probabilistic Zero Certificates for Random Polynomials* (2026).

The whole development is a single file, [`ZeroCertificates.lean`](ZeroCertificates.lean) (about 6,000 lines, namespace `ZeroCert`). It contains **no `sorry` and no `axiom` declarations**.

## What is formalized

All theorems, propositions, lemmas, corollaries and remarks of Sections 2–7 of the paper are proved, including:

- **Section 2:** certificate transfer (Theorem 2.3) and the Vieta lower certificate (Proposition 2.5)
- **Section 3:** monic Cauchy, sub-Weibull, sub-Gaussian, scaled, Fujiwara-type and implicit Cauchy certificates (Theorems 3.1, 3.3, 3.5; Corollaries 3.2, 3.4, 3.6; Proposition 3.7)
- **Section 4:** the exact common-denominator ratio law and its certified radii (Theorem 4.1, Corollary 4.2, Propositions 4.3–4.4, Remark 4.5)
- **Section 5:** the Gumbel limit with moment convergence and the second-order quantile asymptotics (Lemma 5.1, Theorem 5.2, Corollary 5.3)
- **Section 6:** degree-independent small-ball radii, the extreme-root tail, and high-confidence quantiles (Theorems 6.1, 6.4; Corollaries 6.2, 6.5; Remark 6.3)
- **Section 7:** reversed-Cauchy, annular, Rouché and Chernoff certificates (Lemmas 7.1, 7.4; Theorems 7.2, 7.5; Proposition 7.3; Corollary 7.6)

The numerical-experiments section of the paper is not part of the formal development.

[`VERIFICATION.md`](VERIFICATION.md) maps each numbered result of the paper to its Lean theorem name.

## Inputs taken as hypotheses

Three classical deterministic zero bounds are not re-proved. They are stated as propositions and passed as **explicit hypotheses** to every theorem that uses them (never as global axioms):

1. **`CauchyBound`**: the zeros of a monic polynomial with `|a_k| ≤ M` lie in `|z| ≤ 1 + M`.
2. **`VietaBound`**: if all zeros of a monic polynomial lie in `|z| ≤ c`, then `|a_0| ≤ c^n`.
3. **`RoucheLinear`**: Rouché's theorem for a dominant linear term (used for the reversed polynomial in Theorem 6.4 and Corollary 6.5).

Everything else is proved from Mathlib, including the Rouché dominance argument for the leading term, the Gaussian computations, the Cauchy law of Gaussian ratios, the Gumbel limit, the Euler–Mascheroni mean, and the Jensen and Minkowski inequalities.

## Building

Requirements: [Lean 4](https://lean-lang.org/) via `elan`. The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`), and Mathlib is pinned to `v4.28.0` in `lakefile.toml`.

```bash
git clone https://github.com/sajadcosmos/zero-certificates-lean.git
cd zero-certificates-lean
lake update          # resolves Mathlib
lake exe cache get   # downloads precompiled Mathlib
lake build
```

A successful `lake build` with no errors confirms that every proof checks.

An automated build (GitHub Actions, see the **Actions** tab) runs on every change. It compiles the file and prints the axioms of the main theorems, failing if any of them depends on `sorry`.

## Files

| File | Purpose |
|---|---|
| `ZeroCertificates.lean` | The complete formalization |
| `VERIFICATION.md` | Map from the paper's numbered results to Lean theorem names |
| `lakefile.toml` | Lake build configuration (Mathlib dependency) |
| `lean-toolchain` | Pinned Lean version |
| `CITATION.cff` | Citation metadata (powers GitHub's "Cite this repository" button) |
| `.github/workflows/lean.yml` | Automated build and axiom check |

## How to cite

If you use this formalization, please cite it as:

> S. A. Sheikh, *Lean 4 formalization of "Finite-Degree Probabilistic Zero Certificates for Random Polynomials,"* version 1.0, Zenodo (2026), doi:[10.5281/zenodo.23523458](https://doi.org/10.5281/zenodo.23523458).

BibTeX:

```bibtex
@software{sheikh_zero_certificates_lean_2026,
  author    = {Sheikh, Sajad Ahmad},
  title     = {Lean 4 formalization of ``Finite-Degree Probabilistic Zero Certificates for Random Polynomials''},
  version   = {1.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23523458},
  url       = {https://doi.org/10.5281/zenodo.23523458}
}
```

## Contact

Sajad Ahmad Sheikh, Department of Mathematics, University of Kashmir, South Campus, Anantnag, 192101, Jammu and Kashmir, India
sajadsheikh@uok.edu.in

## License

See [`LICENSE`](LICENSE).
