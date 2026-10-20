import Mathlib

section

/-!
# Finite-Degree Probabilistic Zero Certificates for Random Polynomials — complete formalization

This single file formalizes all theorems, propositions, lemmas, corollaries and remarks of
Sections 2–7 of the paper (the numerical-experiments section is deliberately omitted).

## Assumptions

As requested, the classical deterministic zero bounds are *not* proved here; they are stated as
propositions (`CauchyBound`, `VietaBound`, `RoucheLinear`) and passed as explicit hypotheses
to every theorem that uses them:

* `CauchyBound`  — Cauchy's bound: zeros of a monic polynomial with `|a_k| ≤ M` lie in `|z| ≤ 1 + M`;
* `VietaBound`   — Vieta's bound: if all zeros of a monic polynomial lie in `|z| ≤ c`, then
  `|a_0| ≤ c^n`;
* `RoucheLinear` — Rouché's theorem for a dominant *linear* term (used for the reversed polynomial
  in Theorem 6.4 and Corollary 6.5).

All other ingredients (the Rouché dominance argument for the leading term, Gaussian computations,
the Cauchy law of Gaussian ratios, the Gumbel limit, the Euler–Mascheroni mean, Jensen, Minkowski,
etc.) are proved from Mathlib. No `sorry` and no additional axioms are used.

The file is organized in parts following the paper; the section/numbering of each result is
indicated in its docstring.
-/


-- =====================================================================
-- Part: Version-independent helper lemmas
-- =====================================================================

/-!
A few general facts used throughout the file. They are stated and proved here (rather than
quoted from Mathlib by name) so that the file compiles across several Mathlib versions, in which
the corresponding library lemmas have been renamed.
-/

section CompatHelpers

open MeasureTheory

namespace ZeroCert

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- A map into a product is measurable if all its coordinates are. -/
theorem zc_measurable_pi {α δ : Type*} {X : δ → Type*} [MeasurableSpace α]
    [∀ a, MeasurableSpace (X a)] {g : α → ∀ a, X a}
    (h : ∀ a, Measurable fun x => g x a) : Measurable g := by
  first
    | exact measurable_pi_iff.mpr h
    | exact Measurable.of_eval h
    | exact measurable_pi_lambda _ h

/-- A finite sum of integrable real functions is integrable. -/
theorem zc_integrable_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun a => ∑ i ∈ s, f i a) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h1 : Integrable (f j) μ := hf j (Finset.mem_insert_self j s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 : Integrable (fun a => f j a + ∑ i ∈ s, f i a) μ := h1.add h2
    refine h3.congr (ae_of_all _ (fun a => ?_))
    simp only [Finset.sum_insert hj]

/-- The integral of a finite sum of integrable real functions is the sum of the integrals. -/
theorem zc_integral_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h1 : Integrable (f j) μ := hf j (Finset.mem_insert_self j s)
    have hs : ∀ i ∈ s, Integrable (f i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h2 := zc_integrable_finset_sum s hs
    have e : (fun a => ∑ i ∈ insert j s, f i a) = fun a => f j a + ∑ i ∈ s, f i a := by
      funext a; rw [Finset.sum_insert hj]
    rw [e, integral_add h1 h2, ih hs, Finset.sum_insert hj]

/-- Evaluation of a polynomial commutes with finite sums. -/
theorem zc_poly_eval_finset_sum {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (g : ι → Polynomial R) (x : R) :
    (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Polynomial.eval_add, ih]

/-- Coefficients of a polynomial commute with finite sums. -/
theorem zc_poly_finset_sum_coeff {R ι : Type*} [Semiring R] (s : Finset ι)
    (g : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, g i).coeff n = ∑ i ∈ s, (g i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Polynomial.coeff_add, ih]

/-- The image of a probability measure under an a.e.-measurable map is a probability measure. -/
theorem zc_isProbabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f) := by
  constructor
  rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Membership in a set-builder set (version-independent form). -/
theorem zc_mem_setOf_eq {α : Type*} {a : α} {p : α → Prop} : (a ∈ {x | p x}) = p a := rfl

/-- `if` with a true condition (version-independent form). -/
theorem zc_if_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort*} {a b : α} :
    (if c then a else b) = a := by
  cases h with
  | isFalse hn => exact absurd hc hn
  | isTrue _ => rfl

/-- `if` with a false condition (version-independent form). -/
theorem zc_if_neg {c : Prop} [h : Decidable c] (hc : ¬c) {α : Sort*} {a b : α} :
    (if c then a else b) = b := by
  cases h with
  | isFalse _ => rfl
  | isTrue hp => exact absurd hp hc

/-- dependent `if` with a true condition (version-independent form). -/
theorem zc_dif_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort*} {t : c → α} {e : ¬c → α} :
    dite c t e = t hc := by
  cases h with
  | isFalse hn => exact absurd hc hn
  | isTrue _ => rfl

/-- dependent `if` with a false condition (version-independent form). -/
theorem zc_dif_neg {c : Prop} [h : Decidable c] (hc : ¬c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = e hc := by
  cases h with
  | isFalse _ => rfl
  | isTrue hp => exact absurd hp hc

/-- The standard Gaussian law gives zero mass to every point. -/
theorem zc_gauss_singleton (x : ℝ) : ProbabilityTheory.gaussianReal 0 1 {x} = 0 :=
  ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton

end ZeroCert

end CompatHelpers


-- =====================================================================
-- Part: Basic
-- =====================================================================

section

/-!
# Section 2: Certificates and probability transfer
-/

open MeasureTheory ProbabilityTheory Finset

namespace ZeroCert

/-- Evaluation of the polynomial `∑_{k=0}^n a_k z^k`. -/
noncomputable def peval (n : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), a k * z ^ k

/-- All zeros of `∑_{k ≤ n} a_k z^k` lie in the closed disk of radius `c`. -/
def ZerosWithin (n : ℕ) (a : ℕ → ℂ) (c : ℝ) : Prop :=
  ∀ z, peval n a z = 0 → ‖z‖ ≤ c

/-- The outer zero radius `ρ_z(P) = max {|z| : P(z) = 0}`. -/
noncomputable def zeroRadius (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  sSup {r | ∃ z, peval n a z = 0 ∧ ‖z‖ = r}

/-- The inner zero radius `λ_z(P) = min {|z| : P(z) = 0}`. -/
noncomputable def innerRadius (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  sInf {r | ∃ z, peval n a z = 0 ∧ ‖z‖ = r}

/-! ## The classical deterministic ingredients, taken as assumptions -/

/-- **Cauchy's bound** (assumed): every zero of a monic polynomial
`z^n + ∑_{k<n} a_k z^k` with `|a_k| ≤ M` has modulus at most `1 + M`. -/
def CauchyBound : Prop :=
  ∀ (n : ℕ) (a : ℕ → ℂ) (M : ℝ), a n = 1 → (∀ k < n, ‖a k‖ ≤ M) → ZerosWithin n a (1 + M)

/-- **Vieta's bound** (assumed): if all zeros of a monic polynomial of degree `n ≥ 1` lie in the
closed disk of radius `c ≥ 0`, then `|a_0| = |ζ_1 ⋯ ζ_n| ≤ c^n`. -/
def VietaBound : Prop :=
  ∀ (n : ℕ) (a : ℕ → ℂ) (c : ℝ), 1 ≤ n → a n = 1 → 0 ≤ c → ZerosWithin n a c → ‖a 0‖ ≤ c ^ n

/-- **Rouché's theorem for a dominant linear term** (assumed): if on the circle `|w| = r` the
linear term of `∑_{j ≤ n} c_j w^j` strictly dominates the sum of all the other terms, then the
polynomial has a zero in the open disk `|w| < r`. -/
def RoucheLinear : Prop :=
  ∀ (n : ℕ) (c : ℕ → ℂ) (r : ℝ), 1 ≤ n → 0 < r →
    ‖c 0‖ + ∑ j ∈ Ico 2 (n + 1), ‖c j‖ * r ^ j < ‖c 1‖ * r → ∃ w, ‖w‖ < r ∧ peval n c w = 0

/-! ## Elementary facts about zeros -/

lemma peval_eq_eval (n : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    peval n a z = (∑ k ∈ range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k).eval z := by
  simp [peval, zc_poly_eval_finset_sum]

lemma polyOf_coeff (n : ℕ) (a : ℕ → ℂ) :
    (∑ k ∈ range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k).coeff n = a n := by
  rw [zc_poly_finset_sum_coeff]
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

lemma zeroSet_finite (n : ℕ) (a : ℕ → ℂ) (han : a n ≠ 0) :
    {z | peval n a z = 0}.Finite := by
  set p := ∑ k ∈ range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k
  have hp : p ≠ 0 := by
    intro h; apply han; have := polyOf_coeff n a; rw [← this]; simp only [p] at h; rw [h]; simp
  refine (p.roots.toFinset.finite_toSet).subset ?_
  intro z hz
  simp only [ZeroCert.zc_mem_setOf_eq, peval_eq_eval] at hz
  simpa [Polynomial.mem_roots hp] using hz

lemma zeroSet_nonempty (n : ℕ) (a : ℕ → ℂ) (hn : 1 ≤ n) (han : a n ≠ 0) :
    ∃ z, peval n a z = 0 := by
  set p := ∑ k ∈ range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k
  have hdeg : 0 < p.degree := by
    have : p.coeff n ≠ 0 := by rw [polyOf_coeff]; exact han
    have := Polynomial.le_degree_of_ne_zero this
    exact lt_of_lt_of_le (by exact_mod_cast hn) this
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  exact ⟨z, by rw [peval_eq_eval]; exact hz⟩

/-- For a genuine polynomial of degree `n ≥ 1`, `ρ_z ≤ c` iff all zeros lie in the disk. -/
lemma zeroRadius_le_iff (n : ℕ) (a : ℕ → ℂ) (hn : 1 ≤ n) (han : a n ≠ 0) (c : ℝ) :
    zeroRadius n a ≤ c ↔ ZerosWithin n a c := by
  have hfin : {r | ∃ z, peval n a z = 0 ∧ ‖z‖ = r}.Finite := by
    have : {r | ∃ z, peval n a z = 0 ∧ ‖z‖ = r} = (fun z => ‖z‖) '' {z | peval n a z = 0} := by
      ext r; simp
    rw [this]; exact (zeroSet_finite n a han).image _
  obtain ⟨z0, hz0⟩ := zeroSet_nonempty n a hn han
  have hne : {r | ∃ z, peval n a z = 0 ∧ ‖z‖ = r}.Nonempty := ⟨_, z0, hz0, rfl⟩
  unfold zeroRadius ZerosWithin
  rw [csSup_le_iff hfin.bddAbove hne]
  constructor
  · intro h z hz; exact h _ ⟨z, hz, rfl⟩
  · rintro h _ ⟨z, hz, rfl⟩; exact h z hz

/-! ## Measurability of zero-containment events -/

lemma isClosed_exists_zero_in_compact (n : ℕ) (K : Set ℂ) (hK : IsCompact K) :
    IsClosed {a : Fin (n + 1) → ℂ | ∃ z ∈ K, ∑ k : Fin (n + 1), a k * z ^ (k : ℕ) = 0} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcl : IsClosed {p : (Fin (n + 1) → ℂ) × K |
      ∑ k : Fin (n + 1), p.1 k * (p.2 : ℂ) ^ (k : ℕ) = 0} := by
    apply isClosed_eq _ continuous_const
    fun_prop
  have := isClosedMap_fst_of_compactSpace _ hcl
  convert this using 1
  ext a; simp

lemma peval_eq_fin (n : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    peval n a z = ∑ k : Fin (n + 1), a k * z ^ (k : ℕ) := by
  rw [peval, Finset.sum_range]

/-- The event that all zeros lie in the closed disk of radius `c` is measurable. -/
lemma measurableSet_zerosWithin {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (A : ℕ → Ω → ℂ)
    (hA : ∀ k ≤ n, Measurable (A k)) (c : ℝ) :
    MeasurableSet {ω | ZerosWithin n (fun k => A k ω) c} := by
  have hcompl : {ω | ZerosWithin n (fun k => A k ω) c}ᶜ =
      ⋃ m : ℕ, (fun ω (k : Fin (n + 1)) => A k ω) ⁻¹'
        {a : Fin (n + 1) → ℂ | ∃ z ∈ {z : ℂ | c + 1 / ((m : ℝ) + 1) ≤ ‖z‖ ∧ ‖z‖ ≤ m},
          ∑ k : Fin (n + 1), a k * z ^ (k : ℕ) = 0} := by
    ext ω
    simp only [Set.mem_compl_iff, ZeroCert.zc_mem_setOf_eq, ZerosWithin, not_forall, not_le,
      Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · rintro ⟨z, hz, hzc⟩
      obtain ⟨m1, hm1⟩ := exists_nat_one_div_lt (sub_pos.mpr hzc)
      obtain ⟨m2, hm2⟩ := exists_nat_ge ‖z‖
      refine ⟨max m1 m2, z, ⟨?_, ?_⟩, by rw [peval_eq_fin] at hz; exact hz⟩
      · have : 1 / ((max m1 m2 : ℕ) + 1 : ℝ) ≤ 1 / ((m1 : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1
        linarith
      · exact le_trans hm2 (by exact_mod_cast le_max_right _ _)
    · rintro ⟨m, z, ⟨h1, _⟩, hz⟩
      refine ⟨z, by rw [peval_eq_fin]; exact hz, ?_⟩
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  have hmeas : Measurable (fun ω (k : Fin (n + 1)) => A k ω) := by
    rw [measurable_pi_iff]; intro k; exact hA k (Nat.lt_succ_iff.mp k.2)
  rw [← compl_compl {ω | ZerosWithin n (fun k => A k ω) c}, hcompl]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun m => hmeas ?_)
  apply IsClosed.measurableSet
  apply isClosed_exists_zero_in_compact
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := m)).subset
      (fun z hz => by simpa using hz.2)

/-! ## Random polynomials, certificates and transfer -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Zero-containment probability `Π_P(c) = ℙ{ρ_z(P) ≤ c}` (stated as "all zeros in the closed
disk of radius `c`", which agrees with `ρ_z(P) ≤ c` whenever `A_n ≠ 0`, see
`zeroRadius_le_iff`). -/
noncomputable def containProb (μ : Measure Ω) (n : ℕ) (A : ℕ → Ω → ℂ) (c : ℝ) : ℝ :=
  μ.real {ω | ZerosWithin n (fun k => A k ω) c}

/-- Root tail `ℙ{ρ_z(P) > R}`: probability that some zero has modulus larger than `R`. -/
noncomputable def rootTail (μ : Measure Ω) (n : ℕ) (A : ℕ → Ω → ℂ) (R : ℝ) : ℝ :=
  μ.real {ω | ∃ z, peval n (fun k => A k ω) z = 0 ∧ R < ‖z‖}

/-- `c` is a probabilistic zero bound at confidence `p`. -/
def IsProbZeroBound (μ : Measure Ω) (n : ℕ) (A : ℕ → Ω → ℂ) (c p : ℝ) : Prop :=
  p ≤ containProb μ n A c

/-- Outer zero certificate: `ρ_z(P) ≤ B(P)` almost surely. -/
def IsOuterCertificate (μ : Measure Ω) (n : ℕ) (A : ℕ → Ω → ℂ) (B : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ZerosWithin n (fun k => A k ω) (B ω)

/-- Lower certificate for the outer radius: `L(P) ≤ ρ_z(P)` almost surely. -/
def IsLowerCertificate (μ : Measure Ω) (n : ℕ) (A : ℕ → Ω → ℂ) (L : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ c, ZerosWithin n (fun k => A k ω) c → L ω ≤ c

/-- Distribution function of a certificate. -/
noncomputable def certCDF (μ : Measure Ω) (B : Ω → ℝ) (c : ℝ) : ℝ := μ.real {ω | B ω ≤ c}

/-- Certificate radius (quantile). -/
noncomputable def certRadius (μ : Measure Ω) (B : Ω → ℝ) (p : ℝ) : ℝ :=
  sInf {c | 0 ≤ c ∧ p ≤ certCDF μ B c}

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma measureReal_mono_ae' {s t : Set Ω} (h : ∀ᵐ ω ∂μ, ω ∈ s → ω ∈ t) : μ.real s ≤ μ.real t := by
  apply ENNReal.toReal_mono (measure_ne_top μ t)
  apply measure_mono_ae
  filter_upwards [h] with ω hω using hω

/-- **Theorem 2.3 (Certificate transfer).** -/
theorem certificate_transfer (n : ℕ) (A : ℕ → Ω → ℂ) (c : ℝ) :
    (∀ B, IsOuterCertificate μ n A B → certCDF μ B c ≤ containProb μ n A c) ∧
    (∀ L, IsLowerCertificate μ n A L → containProb μ n A c ≤ μ.real {ω | L ω ≤ c}) ∧
    (∀ B p, IsOuterCertificate μ n A B → p ≤ certCDF μ B c → IsProbZeroBound μ n A c p) := by
  have h1 : ∀ B, IsOuterCertificate μ n A B → certCDF μ B c ≤ containProb μ n A c := by
    intro B hB
    apply measureReal_mono_ae'
    filter_upwards [hB] with ω hω hBc z hz
    exact (hω z hz).trans hBc
  refine ⟨h1, ?_, ?_⟩
  · intro L hL
    apply measureReal_mono_ae'
    filter_upwards [hL] with ω hω hc using hω c hc
  · intro B p hB hp
    exact hp.trans (h1 B hB)

/-- **Proposition 2.5 (Vieta lower certificate).** For a monic random polynomial,
`Π_P(c) ≤ ℙ{|a_0| ≤ c^n}`. -/
theorem vieta_lower_certificate (hV : VietaBound) (n : ℕ) (hn : 1 ≤ n) (A : ℕ → Ω → ℂ)
    (hmonic : ∀ ω, A n ω = 1) (c : ℝ) (hc : 0 ≤ c) :
    containProb μ n A c ≤ μ.real {ω | ‖A 0 ω‖ ≤ c ^ n} := by
  apply measureReal_mono_ae'
  filter_upwards with ω hω
  exact hV n (fun k => A k ω) c hn (hmonic ω) hc hω

/-- If the coefficients are measurable, `Π_P(R) + ℙ{ρ_z(P) > R} = 1`. -/
lemma containProb_add_rootTail (n : ℕ) (A : ℕ → Ω → ℂ) (hA : ∀ k ≤ n, Measurable (A k))
    (R : ℝ) :
    containProb μ n A R + rootTail μ n A R = 1 := by
  have hcompl : {ω | ∃ z, peval n (fun k => A k ω) z = 0 ∧ R < ‖z‖} =
      {ω | ZerosWithin n (fun k => A k ω) R}ᶜ := by
    ext ω; simp [ZerosWithin]
  unfold containProb rootTail
  rw [hcompl, measureReal_compl (measurableSet_zerosWithin n A hA R)]
  simp

end ZeroCert

end


-- =====================================================================
-- Part: Monic
-- =====================================================================

section

/-!
# Section 3: Cauchy certificates and monic coefficient laws
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace ZeroCert

variable {Ω : Type*}

/-- Coefficients of the monic polynomial `P_n(z) = z^n + ∑_{k<n} X_k z^k`. -/
noncomputable def monicCoeff (n : ℕ) (X : ℕ → Ω → ℂ) : ℕ → Ω → ℂ :=
  fun k ω => if k = n then 1 else X k ω

lemma monicCoeff_self (n : ℕ) (X : ℕ → Ω → ℂ) (ω : Ω) : monicCoeff n X n ω = 1 := by
  simp [monicCoeff]

lemma monicCoeff_of_lt (n : ℕ) (X : ℕ → Ω → ℂ) (ω : Ω) {k : ℕ} (hk : k < n) :
    monicCoeff n X k ω = X k ω := by
  simp [monicCoeff, hk.ne]

/-- Lower quantile `F^{-1}(u) = inf {t ≥ 0 : F(t) ≥ u}`. -/
noncomputable def lowerQuantile (F : ℝ → ℝ) (u : ℝ) : ℝ := sInf {t | 0 ≤ t ∧ u ≤ F t}

/-- A monotone right-continuous function attains its lower quantile level. -/
lemma le_apply_lowerQuantile (F : ℝ → ℝ) (hmono : Monotone F)
    (hrc : ∀ x, ContinuousWithinAt F (Set.Ici x) x) (u : ℝ)
    (hne : ∃ t, 0 ≤ t ∧ u ≤ F t) : u ≤ F (lowerQuantile F u) := by
  set S := {t | 0 ≤ t ∧ u ≤ F t}
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hSne : S.Nonempty := hne
  set q := lowerQuantile F u
  have key : ∀ ε > 0, u ≤ F (q + ε) := by
    intro ε hε
    obtain ⟨t, ht, htq⟩ := exists_lt_of_csInf_lt hSne (show sInf S < q + ε by
      change q < q + ε; linarith)
    exact ht.2.trans (hmono htq.le)
  have hlim : Tendsto (fun ε => F (q + ε)) (𝓝[>] 0) (𝓝 (F q)) := by
    have h := (hrc q).tendsto
    have h2 : Tendsto (fun ε : ℝ => q + ε) (𝓝[>] 0) (𝓝[≥] q) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun ε : ℝ => q + ε) (𝓝 0) (𝓝 (q + 0)) :=
          tendsto_const_nhds.add tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [Set.mem_Ici]; linarith [Set.mem_Ioi.mp hε]
    exact h.comp h2
  exact ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using key ε hε)

lemma lowerQuantile_nonneg (F : ℝ → ℝ) (u : ℝ) : 0 ≤ lowerQuantile F u := by
  unfold lowerQuantile
  by_cases h : {t | 0 ≤ t ∧ u ≤ F t}.Nonempty
  · exact le_csInf h (fun t ht => ht.1)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Independence turns the probability of a box event into a product. -/
lemma prob_forall_lt_eq_prod (n : ℕ) (X : ℕ → Ω → ℂ)
    (hind : iIndepFun (fun (k : Fin n) => X k) μ) (S : ℕ → Set ℂ)
    (hS : ∀ k, MeasurableSet (S k)) :
    μ.real {ω | ∀ k < n, X k ω ∈ S k} = ∏ k ∈ range n, μ.real {ω | X k ω ∈ S k} := by
  have h := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun k => S k)
    (fun k _ => hS k)
  have hset : {ω | ∀ k < n, X k ω ∈ S k} = ⋂ i ∈ (Finset.univ : Finset (Fin n)),
      (fun (k : Fin n) => X k) i ⁻¹' S i := by
    ext ω; simp only [ZeroCert.zc_mem_setOf_eq, Finset.mem_univ, Set.iInter_true, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩
  rw [Measure.real, hset, h, ENNReal.toReal_prod,
    Finset.prod_range (fun k => μ.real {ω | X k ω ∈ S k})]
  rfl

/-- **Theorem 3.1 (Monic Cauchy certificate).** `Π_{P_n}(c) ≥ H(c-1)^n` for `c ≥ 1`. -/
theorem monic_cauchy_certificate (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℂ)
    (hind : iIndepFun (fun (k : Fin n) => X k) μ)
    (H : ℝ → ℝ) (hH : ∀ k < n, ∀ t, μ.real {ω | ‖X k ω‖ ≤ t} = H t) (c : ℝ) :
    H (c - 1) ^ n ≤ containProb μ n (monicCoeff n X) c := by
  have hprod := prob_forall_lt_eq_prod μ n X hind (fun _ => Metric.closedBall 0 (c - 1))
    (fun _ => Metric.isClosed_closedBall.measurableSet)
  simp only [Metric.mem_closedBall, dist_zero_right] at hprod
  have : ∏ k ∈ range n, μ.real {ω | ‖X k ω‖ ≤ c - 1} = H (c - 1) ^ n := by
    rw [Finset.prod_congr rfl (fun k hk => hH k (Finset.mem_range.mp hk) (c - 1))]
    simp
  rw [← this, ← hprod]
  apply measureReal_mono_ae'
  filter_upwards with ω hω
  have := hC n (fun k => monicCoeff n X k ω) (c - 1) (monicCoeff_self n X ω)
    (fun k hk => by simp only [monicCoeff_of_lt n X ω hk]; exact hω k hk)
  simpa using this

/-- **Theorem 3.1, quantile form.** `c_p = 1 + H^{-1}(p^{1/n})` is a probabilistic zero bound at
confidence `p`, where `H(t) = ℙ{|X| ≤ t}`. -/
theorem monic_cauchy_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℂ)
    (hX0 : Measurable (X 0)) (hind : iIndepFun (fun (k : Fin n) => X k) μ)
    (hident : ∀ k < n, ∀ t, μ.real {ω | ‖X k ω‖ ≤ t} = μ.real {ω | ‖X 0 ω‖ ≤ t})
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsProbZeroBound μ n (monicCoeff n X)
      (1 + lowerQuantile (fun t => μ.real {ω | ‖X 0 ω‖ ≤ t}) (p ^ (1 / (n : ℝ)))) p := by
  set H : ℝ → ℝ := fun t => μ.real {ω | ‖X 0 ω‖ ≤ t}
  set ν := μ.map (fun ω => ‖X 0 ω‖)
  have : IsProbabilityMeasure ν :=
    zc_isProbabilityMeasure_map hX0.norm.aemeasurable
  have hHcdf : ∀ t, H t = cdf ν t := by
    intro t
    rw [cdf_eq_real, Measure.real, Measure.map_apply hX0.norm measurableSet_Iic]
    rfl
  have hmono : Monotone H := by
    intro x y hxy; rw [hHcdf, hHcdf]; exact (cdf ν).mono hxy
  have hrc : ∀ x, ContinuousWithinAt H (Set.Ici x) x := by
    intro x
    have : H = cdf ν := funext hHcdf
    rw [this]; exact (cdf ν).right_continuous x
  set u := p ^ (1 / (n : ℝ))
  have hu1 : u < 1 := Real.rpow_lt_one hp0.le hp1 (by positivity)
  have hne : ∃ t, 0 ≤ t ∧ u ≤ H t := by
    have hlim : Tendsto H atTop (𝓝 1) := by
      have : H = cdf ν := funext hHcdf
      rw [this]; exact tendsto_cdf_atTop ν
    obtain ⟨t, ht⟩ := (hlim.eventually (Ioi_mem_nhds hu1)).exists_forall_of_atTop
    exact ⟨max t 0, le_max_right _ _, (ht _ (le_max_left _ _)).le⟩
  have hq := le_apply_lowerQuantile H hmono hrc u hne
  have hmain := monic_cauchy_certificate μ hC n X hind H (fun k hk t => hident k hk t)
    (1 + lowerQuantile H u)
  simp only [add_sub_cancel_left] at hmain
  unfold IsProbZeroBound
  refine le_trans ?_ hmain
  have hu0 : 0 ≤ u := by positivity
  calc p = u ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
        field_simp
        simp
    _ ≤ H (lowerQuantile H u) ^ n := pow_le_pow_left₀ hu0 hq n

/-- If the complement of an event is covered by `T`, then `ℙ(S) ≥ 1 - ℙ(T)`. -/
lemma one_sub_le_measureReal {S T : Set Ω} (hT : MeasurableSet T) (h : Sᶜ ⊆ T) :
    1 - μ.real T ≤ μ.real S := by
  have : Tᶜ ⊆ S := by intro x hx; by_contra hS; exact hx (h hS)
  calc 1 - μ.real T = μ.real Tᶜ := by rw [measureReal_compl hT]; simp
    _ ≤ μ.real S := measureReal_mono this

/-- **Theorem 3.3 (Sub-Weibull Cauchy radius).** No independence is needed. -/
theorem subWeibull_cauchy_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℂ)
    (hXm : ∀ k, Measurable (X k)) (A K α : ℝ) (hA : 1 ≤ A) (hK : 0 < K) (hα : 0 < α)
    (htail : ∀ k < n, ∀ t, 0 ≤ t → μ.real {ω | t < ‖X k ω‖} ≤ A * Real.exp (-(t / K) ^ α))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ containProb μ n (monicCoeff n X)
      (1 + K * (Real.log (A * n / δ)) ^ (1 / α)) := by
  set L := Real.log (A * n / δ)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  set t := K * L ^ (1 / α)
  have ht0 : 0 ≤ t := by positivity
  have htK : (t / K) ^ α = L := by
    rw [show t / K = L ^ (1 / α) from mul_div_cancel_left₀ _ hK.ne']
    rw [← Real.rpow_mul hL, one_div_mul_cancel hα.ne', Real.rpow_one]
  have hcov : {ω | ZerosWithin n (fun k => monicCoeff n X k ω) (1 + t)}ᶜ ⊆
      ⋃ k ∈ range n, {ω | t < ‖X k ω‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, ZeroCert.zc_mem_setOf_eq, not_exists, not_lt, Finset.mem_range] at hcon
    apply hω
    exact hC n (fun k => monicCoeff n X k ω) t (monicCoeff_self n X ω)
      (fun k hk => by simp only [monicCoeff_of_lt n X ω hk]; exact hcon k hk)
  have hmeas : MeasurableSet (⋃ k ∈ range n, {ω | t < ‖X k ω‖}) :=
    Finset.measurableSet_biUnion _ (fun k _ => measurableSet_lt measurable_const (hXm k).norm)
  have h1 := one_sub_le_measureReal μ hmeas hcov
  have h2 : μ.real (⋃ k ∈ range n, {ω | t < ‖X k ω‖}) ≤ δ := by
    calc μ.real (⋃ k ∈ range n, {ω | t < ‖X k ω‖})
        ≤ ∑ k ∈ range n, μ.real {ω | t < ‖X k ω‖} := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ range n, A * Real.exp (-(t / K) ^ α) :=
          Finset.sum_le_sum (fun k hk => htail k (Finset.mem_range.mp hk) t ht0)
      _ = δ := by
          rw [htK, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.exp_neg,
            Real.exp_log (by
              have : (0 : ℝ) < n := by exact_mod_cast hn
              positivity)]
          have : (0 : ℝ) < n := by exact_mod_cast hn
          field_simp
  unfold containProb
  linarith

/-- **Corollary 3.4 (Sub-Gaussian radius).** -/
theorem subGaussian_cauchy_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℂ)
    (hXm : ∀ k, Measurable (X k)) (σ : ℝ) (hσ : 0 < σ)
    (htail : ∀ k < n, ∀ t, 0 ≤ t → μ.real {ω | t < ‖X k ω‖} ≤ 2 * Real.exp (-t ^ 2 / (2 * σ ^ 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ containProb μ n (monicCoeff n X) (1 + σ * Real.sqrt (2 * Real.log (2 * n / δ))) := by
  have h := subWeibull_cauchy_radius μ hC n hn X hXm 2 (σ * Real.sqrt 2) 2 (by norm_num)
    (by positivity) (by norm_num) (fun k hk t ht => by
      convert htail k hk t ht using 3
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, mul_pow,
        Real.sq_sqrt (by norm_num)]
      ring) δ hδ0 hδ1
  convert h using 3
  have hL : 0 ≤ Real.log (2 * n / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [Real.sqrt_mul (by norm_num), ← Real.sqrt_eq_rpow, mul_assoc]

end ZeroCert

end


-- =====================================================================
-- Part: Scaled
-- =====================================================================

section

/-!
# Section 3 (continued): scaled Cauchy certificates, the implicit Cauchy radius and the
deterministic ordering
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace ZeroCert

/-- The scaled Cauchy certificate `B_s(P) = s (1 + max_{k<n} |a_k| s^{k-n})`. -/
noncomputable def scaledCauchy (n : ℕ) (a : ℕ → ℂ) (s : ℝ) : ℝ :=
  s * (1 + ⨆ k : Fin n, ‖a k‖ * s ^ ((k : ℤ) - n))

/-- The optimized scaled envelope `B_opt(P) = inf_{s>0} B_s(P)`. -/
noncomputable def optScaledCauchy (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  ⨅ s : Set.Ioi (0 : ℝ), scaledCauchy n a s

/-- Fujiwara's quantity `M_F = max_{k<n} |a_k|^{1/(n-k)}`. -/
noncomputable def fujiwaraM (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  ⨆ k : Fin n, ‖a k‖ ^ (1 / ((n : ℝ) - k))

/-- The explicit Cauchy bound `B_C(P) = 1 + max_{k<n} |a_k|`. -/
noncomputable def explicitCauchy (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  1 + ⨆ k : Fin n, ‖a k‖

/-- `F(R) = ∑_{k<n} b_k R^{k-n}`, written as `∑_{k<n} b_k (R⁻¹)^{n-k}`. -/
noncomputable def cauchyF (n : ℕ) (b : ℕ → ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ range n, b k * (R⁻¹) ^ (n - k)

/-- The implicit Cauchy radius `B_R`: the positive solution of `∑_{k<n} b_k B^{k-n} = 1`
(and `0` if all `b_k` vanish), defined as `inf {R > 0 : F(R) ≤ 1}`. -/
noncomputable def implicitCauchy (n : ℕ) (b : ℕ → ℝ) : ℝ :=
  sInf {R | 0 < R ∧ cauchyF n b R ≤ 1}

/-! ### Scaled certificates -/

lemma iSup_fin_nonneg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ k, 0 ≤ f k) : 0 ≤ ⨆ k, f k :=
  Real.iSup_nonneg hf

lemma le_iSup_fin {n : ℕ} (f : Fin n → ℝ) (k : Fin n) : f k ≤ ⨆ k, f k :=
  le_ciSup (Set.finite_range f).bddAbove k

lemma scaledCauchy_nonneg (n : ℕ) (a : ℕ → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ scaledCauchy n a s := by
  unfold scaledCauchy
  have : 0 ≤ ⨆ k : Fin n, ‖a k‖ * s ^ ((k : ℤ) - n) :=
    iSup_fin_nonneg _ (fun k => mul_nonneg (norm_nonneg _) (zpow_nonneg hs _))
  positivity

lemma peval_scaled (n : ℕ) (a : ℕ → ℂ) (s : ℝ) (hs : 0 < s) (z : ℂ) :
    peval n (fun k => a k * ((s : ℂ) ^ ((k : ℤ) - n))) (z / s) =
      (s : ℂ) ^ (-(n : ℤ)) * peval n a z := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold peval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  try dsimp only
  rw [div_pow, zpow_sub₀ hs', zpow_neg, zpow_natCast, zpow_natCast]
  field_simp

/-- **Theorem 3.5 (i).** Each scaled certificate `B_s`, `s > 0`, is an outer certificate. -/
theorem zerosWithin_scaledCauchy (hC : CauchyBound) (n : ℕ) (a : ℕ → ℂ) (han : a n = 1)
    (s : ℝ) (hs : 0 < s) : ZerosWithin n a (scaledCauchy n a s) := by
  intro z hz
  set M := ⨆ k : Fin n, ‖a k‖ * s ^ ((k : ℤ) - n)
  have hb : (fun k => a k * ((s : ℂ) ^ ((k : ℤ) - n))) n = 1 := by simp [han]
  have hM : ∀ k < n, ‖(fun k => a k * ((s : ℂ) ^ ((k : ℤ) - n))) k‖ ≤ M := by
    intro k hk
    simp only [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact le_iSup_fin (fun k : Fin n => ‖a k‖ * s ^ ((k : ℤ) - n)) ⟨k, hk⟩
  have hzero : peval n (fun k => a k * ((s : ℂ) ^ ((k : ℤ) - n))) (z / s) = 0 := by
    rw [peval_scaled n a s hs z, hz, mul_zero]
  have := hC n _ M hb hM (z / s) hzero
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_le_iff₀ hs] at this
  unfold scaledCauchy
  linarith

lemma scaledCauchy_bddBelow (n : ℕ) (a : ℕ → ℂ) :
    BddBelow (Set.range fun s : Set.Ioi (0 : ℝ) => scaledCauchy n a s) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; exact scaledCauchy_nonneg n a (le_of_lt s.2)⟩

/-- **Theorem 3.5 (ii).** The envelope `B_opt` is an outer certificate. -/
theorem zerosWithin_optScaledCauchy (hC : CauchyBound) (n : ℕ) (a : ℕ → ℂ) (han : a n = 1) :
    ZerosWithin n a (optScaledCauchy n a) := by
  intro z hz
  unfold optScaledCauchy
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  exact le_ciInf (fun s => zerosWithin_scaledCauchy hC n a han s s.2 z hz)

lemma optScaledCauchy_le (n : ℕ) (a : ℕ → ℂ) {s : ℝ} (hs : 0 < s) :
    optScaledCauchy n a ≤ scaledCauchy n a s :=
  ciInf_le (scaledCauchy_bddBelow n a) ⟨s, hs⟩

lemma optScaledCauchy_nonneg (n : ℕ) (a : ℕ → ℂ) : 0 ≤ optScaledCauchy n a := by
  unfold optScaledCauchy
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  exact le_ciInf (fun s => scaledCauchy_nonneg n a (le_of_lt s.2))

lemma norm_le_fujiwara_pow (n : ℕ) (a : ℕ → ℂ) (k : ℕ) (hk : k < n) :
    ‖a k‖ ≤ fujiwaraM n a ^ (n - k) := by
  have hm : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hk
  have hcast : ((n : ℝ) - k) = ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk.le]
  have h1 : ‖a k‖ ^ (1 / ((n : ℝ) - k)) ≤ fujiwaraM n a :=
    le_iSup_fin (fun k : Fin n => ‖a k‖ ^ (1 / ((n : ℝ) - k))) ⟨k, hk⟩
  have h0 : 0 ≤ ‖a k‖ ^ (1 / ((n : ℝ) - k)) := by positivity
  calc ‖a k‖ = (‖a k‖ ^ (1 / ((n : ℝ) - k))) ^ (n - k) := by
        rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        rw [one_div_mul_cancel hm.ne', Real.rpow_one]
    _ ≤ fujiwaraM n a ^ (n - k) := pow_le_pow_left₀ h0 h1 _

/-- **Theorem 3.5 (iii).** Fujiwara-type bound `B_opt(P) ≤ 2 M_F`. -/
theorem optScaledCauchy_le_two_fujiwara (n : ℕ) (a : ℕ → ℂ) :
    optScaledCauchy n a ≤ 2 * fujiwaraM n a := by
  have hMF0 : 0 ≤ fujiwaraM n a := iSup_fin_nonneg _ (fun k => by positivity)
  rcases hMF0.lt_or_eq with hpos | hzero
  · refine (optScaledCauchy_le n a hpos).trans ?_
    unfold scaledCauchy
    have hsup : (⨆ k : Fin n, ‖a k‖ * fujiwaraM n a ^ ((k : ℤ) - n)) ≤ 1 := by
      apply Real.iSup_le _ zero_le_one
      intro k
      have h := norm_le_fujiwara_pow n a k k.2
      have hzp : fujiwaraM n a ^ ((k : ℤ) - n) * fujiwaraM n a ^ (n - (k : ℕ)) = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ hpos.ne', Nat.cast_sub k.2.le]
        simp
      calc ‖a k‖ * fujiwaraM n a ^ ((k : ℤ) - n)
          ≤ fujiwaraM n a ^ (n - (k : ℕ)) * fujiwaraM n a ^ ((k : ℤ) - n) :=
            mul_le_mul_of_nonneg_right h (zpow_nonneg hpos.le _)
        _ = 1 := by rw [mul_comm]; exact hzp
    nlinarith
  · rw [← hzero, mul_zero]
    have hak : ∀ k < n, a k = 0 := by
      intro k hk
      have h := norm_le_fujiwara_pow n a k hk
      rw [← hzero, zero_pow (Nat.sub_pos_of_lt hk).ne'] at h
      exact norm_le_zero_iff.mp h
    apply le_of_forall_pos_le_add
    intro ε hε
    refine (optScaledCauchy_le n a hε).trans (le_of_eq ?_)
    unfold scaledCauchy
    have : (⨆ k : Fin n, ‖a k‖ * ε ^ ((k : ℤ) - n)) = 0 := by
      have : (fun k : Fin n => ‖a k‖ * ε ^ ((k : ℤ) - n)) = fun _ => 0 := by
        funext k; rw [hak k k.2]; simp
      rw [this]; exact Real.iSup_const_zero
    rw [this]; ring

/-! ### The implicit Cauchy radius -/

/-- `G(u) = ∑_{k<n} b_k u^{n-k}`, so that `F(R) = G(R⁻¹)`. -/
noncomputable def cauchyG (n : ℕ) (b : ℕ → ℝ) (u : ℝ) : ℝ := ∑ k ∈ range n, b k * u ^ (n - k)

lemma cauchyF_eq (n : ℕ) (b : ℕ → ℝ) (R : ℝ) : cauchyF n b R = cauchyG n b R⁻¹ := rfl

lemma cauchyG_continuous (n : ℕ) (b : ℕ → ℝ) : Continuous (cauchyG n b) := by
  unfold cauchyG; fun_prop

lemma cauchyG_zero (n : ℕ) (b : ℕ → ℝ) : cauchyG n b 0 = 0 := by
  unfold cauchyG
  exact Finset.sum_eq_zero (fun k hk => by
    rw [zero_pow (Nat.sub_pos_of_lt (Finset.mem_range.mp hk)).ne', mul_zero])

lemma cauchyG_mono (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) : cauchyG n b u ≤ cauchyG n b v := by
  unfold cauchyG
  exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hu huv _) (hb k (Finset.mem_range.mp hk)))

lemma cauchyG_strictMono (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k) (k0 : ℕ) (hk0 : k0 < n)
    (hbk0 : 0 < b k0) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    cauchyG n b u < cauchyG n b v := by
  unfold cauchyG
  apply Finset.sum_lt_sum
  · intro k hk
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv.le _)
      (hb k (Finset.mem_range.mp hk))
  · refine ⟨k0, Finset.mem_range.mpr hk0, ?_⟩
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ huv hu (Nat.sub_pos_of_lt hk0).ne') hbk0

lemma exists_cauchyG_eq_one (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k) (k0 : ℕ)
    (hk0 : k0 < n) (hbk0 : 0 < b k0) : ∃ u, 0 < u ∧ cauchyG n b u = 1 := by
  set U := max 1 (1 / b k0)
  have hU1 : 1 ≤ U := le_max_left _ _
  have hGU : 1 ≤ cauchyG n b U := by
    have hterm : b k0 * U ^ (n - k0) ≤ cauchyG n b U := by
      unfold cauchyG
      exact Finset.single_le_sum (f := fun k => b k * U ^ (n - k))
        (fun k hk => mul_nonneg (hb k (Finset.mem_range.mp hk)) (by positivity))
        (Finset.mem_range.mpr hk0)
    have hpow : U ≤ U ^ (n - k0) := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ (n - k0) := pow_le_pow_right₀ hU1 (Nat.sub_pos_of_lt hk0)
    have : 1 ≤ b k0 * U := by
      have : 1 / b k0 ≤ U := le_max_right _ _
      rw [div_le_iff₀ hbk0] at this; linarith
    nlinarith
  obtain ⟨u, hu, hGu⟩ := intermediate_value_Icc (zero_le_one.trans hU1)
    (cauchyG_continuous n b).continuousOn ⟨by rw [cauchyG_zero]; norm_num, hGU⟩
  refine ⟨u, ?_, hGu⟩
  rcases hu.1.lt_or_eq with h | h
  · exact h
  · rw [← h, cauchyG_zero] at hGu; norm_num at hGu

/-- **Proposition 3.7 (well-definedness).** If some `b_k ≠ 0`, the implicit Cauchy radius is the
unique positive solution of `∑_{k<n} b_k B^{k-n} = 1`. -/
theorem implicitCauchy_spec (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k)
    (hne : ∃ k < n, b k ≠ 0) :
    0 < implicitCauchy n b ∧ cauchyF n b (implicitCauchy n b) = 1 ∧
      ∀ R, 0 < R → cauchyF n b R = 1 → R = implicitCauchy n b := by
  obtain ⟨k0, hk0, hbk0'⟩ := hne
  have hbk0 : 0 < b k0 := lt_of_le_of_ne (hb k0 hk0) (Ne.symm hbk0')
  obtain ⟨u, hu, hGu⟩ := exists_cauchyG_eq_one n b hb k0 hk0 hbk0
  have hset : {R | 0 < R ∧ cauchyF n b R ≤ 1} = Set.Ici u⁻¹ := by
    ext R
    simp only [ZeroCert.zc_mem_setOf_eq, Set.mem_Ici, cauchyF_eq]
    constructor
    · rintro ⟨hR, hle⟩
      by_contra hlt
      push Not at hlt
      have : u < R⁻¹ := by
        rw [lt_inv_comm₀ hu hR]; exact hlt
      have := cauchyG_strictMono n b hb k0 hk0 hbk0 hu.le this
      linarith
    · intro hR
      have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.mpr hu) hR
      refine ⟨hRpos, ?_⟩
      rw [← hGu]
      apply cauchyG_mono n b hb (inv_nonneg.mpr hRpos.le)
      rw [inv_le_comm₀ hRpos hu]; exact hR
  have hB : implicitCauchy n b = u⁻¹ := by
    unfold implicitCauchy; rw [hset, csInf_Ici]
  refine ⟨by rw [hB]; exact inv_pos.mpr hu, by rw [hB, cauchyF_eq, inv_inv, hGu], ?_⟩
  intro R hR hFR
  rw [hB]
  rw [cauchyF_eq] at hFR
  rcases lt_trichotomy R⁻¹ u with h | h | h
  · have := cauchyG_strictMono n b hb k0 hk0 hbk0 (inv_nonneg.mpr hR.le) h; linarith
  · rw [← h, inv_inv]
  · have := cauchyG_strictMono n b hb k0 hk0 hbk0 hu.le h; linarith

/-- If all `b_k` vanish then `B_R = 0` (the convention `B_R(z^n) = 0`). -/
theorem implicitCauchy_eq_zero (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, b k = 0) :
    implicitCauchy n b = 0 := by
  have hset : {R | 0 < R ∧ cauchyF n b R ≤ 1} = Set.Ioi 0 := by
    ext R
    simp only [ZeroCert.zc_mem_setOf_eq, Set.mem_Ioi, and_iff_left_iff_imp]
    intro _
    unfold cauchyF
    rw [Finset.sum_eq_zero (fun k hk => by rw [hb k (Finset.mem_range.mp hk), zero_mul])]
    norm_num
  unfold implicitCauchy; rw [hset, csInf_Ioi]

lemma implicitCauchy_nonneg (n : ℕ) (b : ℕ → ℝ) : 0 ≤ implicitCauchy n b := by
  unfold implicitCauchy
  by_cases h : {R | 0 < R ∧ cauchyF n b R ≤ 1}.Nonempty
  · exact le_csInf h (fun R hR => hR.1.le)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

lemma implicitCauchy_congr (n : ℕ) (b c : ℕ → ℝ) (h : ∀ k < n, b k = c k) :
    implicitCauchy n b = implicitCauchy n c := by
  have : ∀ R, cauchyF n b R = cauchyF n c R := fun R =>
    Finset.sum_congr rfl (fun k hk => by rw [h k (Finset.mem_range.mp hk)])
  unfold implicitCauchy
  simp_rw [this]

/-- A zero `z ≠ 0` of a monic polynomial satisfies `1 ≤ G(|z|⁻¹)`. -/
lemma one_le_cauchyG_of_zero (n : ℕ) (a : ℕ → ℂ) (han : a n = 1) (z : ℂ) (hz0 : z ≠ 0)
    (hz : peval n a z = 0) : 1 ≤ cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  unfold peval at hz
  rw [Finset.sum_range_succ, han, one_mul] at hz
  have h1 : z ^ n = -∑ k ∈ range n, a k * z ^ k := by linear_combination hz
  have h2 : ‖z‖ ^ n ≤ ∑ k ∈ range n, ‖a k‖ * ‖z‖ ^ k := by
    rw [← norm_pow, h1, norm_neg]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have h3 : cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ = (∑ k ∈ range n, ‖a k‖ * ‖z‖ ^ k) / ‖z‖ ^ n := by
    unfold cauchyG
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    rw [inv_pow, mul_div_assoc]
    congr 1
    rw [show n = (n - k) + k from (Nat.sub_add_cancel hk.le).symm, pow_add]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [h3, le_div_iff₀ (by positivity), one_mul]
  exact h2

/-- **Proposition 3.7, first inequality.** `ρ_z(P) ≤ B_R(P)` (no assumption needed). -/
theorem zerosWithin_implicitCauchy (n : ℕ) (a : ℕ → ℂ) (han : a n = 1) :
    ZerosWithin n a (implicitCauchy n (fun k => ‖a k‖)) := by
  intro z hz
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero]; exact implicitCauchy_nonneg _ _
  have hG := one_le_cauchyG_of_zero n a han z hz0 hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  by_cases hne : ∃ k < n, ‖a k‖ ≠ 0
  · obtain ⟨hBpos, hBF, _⟩ := implicitCauchy_spec n (fun k => ‖a k‖)
      (fun k _ => norm_nonneg _) hne
    obtain ⟨k0, hk0, hbk0'⟩ := hne
    have hbk0 : 0 < ‖a k0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hbk0')
    by_contra hlt
    push Not at hlt
    have : ‖z‖⁻¹ < (implicitCauchy n (fun k => ‖a k‖))⁻¹ := inv_strictAnti₀ hBpos hlt
    have := cauchyG_strictMono n (fun k => ‖a k‖) (fun k _ => norm_nonneg _) k0 hk0 hbk0
      (inv_nonneg.mpr hzn.le) this
    rw [cauchyF_eq] at hBF
    linarith
  · push Not at hne
    have : cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ = 0 := by
      unfold cauchyG
      exact Finset.sum_eq_zero (fun k hk => by simp [hne k (Finset.mem_range.mp hk)])
    linarith

/-- The extremal polynomial `P_-(z) = z^n - ∑_{k<n} b_k z^k`. -/
noncomputable def negPoly (n : ℕ) (b : ℕ → ℝ) : ℕ → ℂ := fun k => if k = n then 1 else -(b k : ℂ)

lemma negPoly_zero_at_implicitCauchy (n : ℕ) (hn : 1 ≤ n) (b : ℕ → ℝ)
    (hb : ∀ k < n, 0 ≤ b k) :
    peval n (negPoly n b) (implicitCauchy n b) = 0 := by
  unfold peval
  rw [Finset.sum_range_succ]
  simp only [negPoly]
  have hsum : ∑ x ∈ range n, (if x = n then (1 : ℂ) else -(b x : ℂ)) * (implicitCauchy n b : ℂ) ^ x
      = -∑ x ∈ range n, (b x : ℂ) * (implicitCauchy n b : ℂ) ^ x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k hk => by
      rw [ZeroCert.zc_if_neg (Finset.mem_range.mp hk).ne]; ring)
  rw [hsum]
  by_cases hne : ∃ k < n, b k ≠ 0
  · obtain ⟨hBpos, hBF, _⟩ := implicitCauchy_spec n b hb hne
    set B := implicitCauchy n b
    have hreal : ∑ x ∈ range n, b x * B ^ x = B ^ n := by
      have h := hBF
      unfold cauchyF at h
      have : ∑ k ∈ range n, b k * B⁻¹ ^ (n - k) * B ^ n = B ^ n := by
        rw [← Finset.sum_mul, h, one_mul]
      rw [← this]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk := Finset.mem_range.mp hk
      rw [show n = (n - k) + k from (Nat.sub_add_cancel hk.le).symm, pow_add]
      simp only [Nat.add_sub_cancel]
      rw [inv_pow]
      field_simp
    have : ∑ x ∈ range n, (b x : ℂ) * (B : ℂ) ^ x = ((B ^ n : ℝ) : ℂ) := by
      rw [← hreal]; push_cast; rfl
    rw [this]; push_cast; ring
  · push Not at hne
    rw [implicitCauchy_eq_zero n b hne]
    simp only [Complex.ofReal_zero]
    rw [zero_pow (by omega), Finset.sum_eq_zero (fun k hk => by
      rw [hne k (Finset.mem_range.mp hk)]; simp)]
    simp

lemma scaledCauchy_congr (n : ℕ) (a c : ℕ → ℂ) (h : ∀ k < n, ‖a k‖ = ‖c k‖) (s : ℝ) :
    scaledCauchy n a s = scaledCauchy n c s := by
  unfold scaledCauchy
  congr 2
  exact iSup_congr (fun k => by rw [h k k.2])

/-- **Proposition 3.7 (deterministic ordering).**
`ρ_z(P) ≤ B_R(P) ≤ B_opt(P) ≤ B_C(P)`. -/
theorem cauchy_hierarchy (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n = 1) :
    ZerosWithin n a (implicitCauchy n (fun k => ‖a k‖)) ∧
    implicitCauchy n (fun k => ‖a k‖) ≤ optScaledCauchy n a ∧
    optScaledCauchy n a ≤ explicitCauchy n a := by
  refine ⟨zerosWithin_implicitCauchy n a han, ?_, ?_⟩
  · set b : ℕ → ℝ := fun k => ‖a k‖
    unfold optScaledCauchy
    have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
    apply le_ciInf
    intro s
    have hz := negPoly_zero_at_implicitCauchy n hn b (fun k _ => norm_nonneg _)
    have := zerosWithin_scaledCauchy hC n (negPoly n b) (by simp [negPoly]) s s.2 _ hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (implicitCauchy_nonneg _ _)] at this
    rw [scaledCauchy_congr n (negPoly n b) a (fun k hk => by
      simp [negPoly, hk.ne, b]) s] at this
    exact this
  · refine (optScaledCauchy_le n a one_pos).trans (le_of_eq ?_)
    unfold scaledCauchy explicitCauchy
    simp

/-- **Proposition 3.7 (magnitude-only optimality).** For fixed magnitudes `b_k ≥ 0`,
`sup_{|a_k| = b_k} ρ_z(z^n + ∑ a_k z^k) = B_R(b)`, and the supremum is attained. -/
theorem implicitCauchy_isGreatest (n : ℕ) (hn : 1 ≤ n) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k) :
    IsGreatest {r | ∃ a : ℕ → ℂ, a n = 1 ∧ (∀ k < n, ‖a k‖ = b k) ∧ zeroRadius n a = r}
      (implicitCauchy n b) := by
  constructor
  · refine ⟨negPoly n b, by simp [negPoly], fun k hk => by
      simp [negPoly, hk.ne, abs_of_nonneg (hb k hk)], ?_⟩
    have hne : negPoly n b n ≠ 0 := by simp [negPoly]
    apply le_antisymm
    · rw [zeroRadius_le_iff n _ hn hne]
      have := zerosWithin_implicitCauchy n (negPoly n b) (by simp [negPoly])
      rwa [implicitCauchy_congr n (fun k => ‖negPoly n b k‖) b (fun k hk => by
        simp [negPoly, hk.ne, abs_of_nonneg (hb k hk)])] at this
    · have hfin : {r | ∃ z, peval n (negPoly n b) z = 0 ∧ ‖z‖ = r}.Finite := by
        have : {r | ∃ z, peval n (negPoly n b) z = 0 ∧ ‖z‖ = r} =
            (fun z => ‖z‖) '' {z | peval n (negPoly n b) z = 0} := by ext r; simp
        rw [this]; exact (zeroSet_finite n _ hne).image _
      apply le_csSup hfin.bddAbove
      refine ⟨(implicitCauchy n b : ℂ), negPoly_zero_at_implicitCauchy n hn b hb, ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (implicitCauchy_nonneg _ _)]
  · rintro r ⟨a, han, hab, rfl⟩
    rw [zeroRadius_le_iff n a hn (by rw [han]; exact one_ne_zero)]
    have := zerosWithin_implicitCauchy n a han
    rwa [implicitCauchy_congr n (fun k => ‖a k‖) b hab] at this

/-! ### Probabilistic Fujiwara-type certificate -/

lemma zerosWithin_of_fujiwara (n : ℕ) (a : ℕ → ℂ) (hC : CauchyBound) (han : a n = 1) (c : ℝ)
    (hc : 0 < c) (h : ∀ k < n, ‖a k‖ ≤ (c / 2) ^ (n - k)) : ZerosWithin n a c := by
  have hMF : fujiwaraM n a ≤ c / 2 := by
    apply Real.iSup_le _ (by linarith)
    intro k
    have hm : (0 : ℝ) < ((n - (k : ℕ) : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt k.2
    have hcast : ((n : ℝ) - k) = ((n - (k : ℕ) : ℕ) : ℝ) := by rw [Nat.cast_sub k.2.le]
    calc ‖a k‖ ^ (1 / ((n : ℝ) - k)) ≤ ((c / 2) ^ (n - (k : ℕ))) ^ (1 / ((n : ℝ) - k)) :=
          Real.rpow_le_rpow (norm_nonneg _) (h k k.2) (by rw [hcast]; positivity)
      _ = c / 2 := by
          rw [hcast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
            mul_one_div_cancel hm.ne', Real.rpow_one]
  intro z hz
  have h1 := zerosWithin_optScaledCauchy hC n a han z hz
  have h2 := optScaledCauchy_le_two_fujiwara n a
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Corollary 3.6 (Fujiwara-type probabilistic certificate).**
`Π_{P_n}(c) ≥ ∏_{j=1}^n H((c/2)^j)` for `c > 0`. -/
theorem fujiwara_certificate (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℂ)
    (hind : iIndepFun (fun (k : Fin n) => X k) μ)
    (H : ℝ → ℝ) (hH : ∀ k < n, ∀ t, μ.real {ω | ‖X k ω‖ ≤ t} = H t) (c : ℝ) (hc : 0 < c) :
    ∏ j ∈ Finset.Icc 1 n, H ((c / 2) ^ j) ≤ containProb μ n (monicCoeff n X) c := by
  have hprod := prob_forall_lt_eq_prod μ n X hind
    (fun k => Metric.closedBall 0 ((c / 2) ^ (n - k)))
    (fun _ => Metric.isClosed_closedBall.measurableSet)
  simp only [Metric.mem_closedBall, dist_zero_right] at hprod
  have hre : ∏ j ∈ Finset.Icc 1 n, H ((c / 2) ^ j) =
      ∏ k ∈ range n, μ.real {ω | ‖X k ω‖ ≤ (c / 2) ^ (n - k)} := by
    rw [Finset.prod_congr rfl (fun k hk => hH k (Finset.mem_range.mp hk) _)]
    rw [← Finset.prod_range_reflect (fun k => H ((c / 2) ^ (n - k)))]
    have : Finset.Icc 1 n = (range n).image (fun j => j + 1) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨j - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.prod_image (fun x _ y _ h => by omega)]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    congr 2; omega
  rw [hre, ← hprod]
  apply measureReal_mono_ae'
  filter_upwards with ω hω
  exact zerosWithin_of_fujiwara n _ hC (monicCoeff_self n X ω) c hc
    (fun k hk => by rw [monicCoeff_of_lt n X ω hk]; exact hω k hk)

end ZeroCert

end


-- =====================================================================
-- Part: Gaussian
-- =====================================================================

section

/-!
# Half-normal distribution function, `erf`, and independence tools
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- `h₀ = √(2/π)`. -/
noncomputable def h0 : ℝ := √(2 / π)

/-- Half-normal density `h(t) = √(2/π) e^{-t²/2}`. -/
noncomputable def hnDens (t : ℝ) : ℝ := h0 * exp (-t ^ 2 / 2)

/-- Half-normal distribution function `H(t) = ℙ{|N(0,1)| ≤ t}`. -/
noncomputable def hnCDF (t : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Icc (-t) t)

/-- The error function `erf(x) = (2/√π) ∫_0^x e^{-s²} ds`. -/
noncomputable def erf (x : ℝ) : ℝ := 2 / √π * ∫ s in (0 : ℝ)..x, exp (-s ^ 2)

lemma h0_pos : 0 < h0 := by unfold h0; positivity

lemma h0_sq : h0 ^ 2 = 2 / π := by
  unfold h0; rw [sq_sqrt (by positivity)]

lemma hnDens_pos (t : ℝ) : 0 < hnDens t := by unfold hnDens; have := h0_pos; positivity

lemma hnDens_le (t : ℝ) : hnDens t ≤ h0 := by
  unfold hnDens
  have : exp (-t ^ 2 / 2) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith [sq_nonneg t]
  have := h0_pos
  nlinarith

lemma hnDens_continuous : Continuous hnDens := by unfold hnDens; fun_prop

lemma gaussianPDFReal_std (x : ℝ) : gaussianPDFReal 0 1 x = hnDens x / 2 := by
  rw [gaussianPDFReal_def, hnDens, h0]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have : √(2 / π) / 2 = (√(2 * π))⁻¹ := by
    rw [sqrt_div (by norm_num), sqrt_mul (by norm_num)]
    have h2 : (0 : ℝ) < √2 := by positivity
    have hp : (0 : ℝ) < √π := by positivity
    field_simp
    rw [sq_sqrt (by norm_num)]
  rw [show √(2 / π) * rexp (-x ^ 2 / 2) / 2 = (√(2 / π) / 2) * rexp (-x ^ 2 / 2) by ring, this]

lemma stdGauss_real_apply (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ x in s, gaussianPDFReal 0 1 x := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero s, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg_of_ae (ae_of_all _ (fun x => gaussianPDFReal_nonneg 0 1 x))

lemma intervalIntegrable_hnDens (a b : ℝ) : IntervalIntegrable hnDens volume a b :=
  hnDens_continuous.intervalIntegrable a b

/-- `H(t) = ∫_0^t h` for `t ≥ 0`. -/
lemma hnCDF_eq_integral {t : ℝ} (ht : 0 ≤ t) : hnCDF t = ∫ u in (0 : ℝ)..t, hnDens u := by
  unfold hnCDF
  rw [stdGauss_real_apply, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (by linarith)]
  simp_rw [gaussianPDFReal_std]
  have hc : Continuous fun x => hnDens x / 2 := hnDens_continuous.div_const 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg : ∫ x in (-t)..0, hnDens x / 2 = ∫ x in (0 : ℝ)..t, hnDens x / 2 := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := t) (fun x => hnDens x / 2)
    rw [neg_zero] at this
    rw [← this]
    congr 1; funext x; simp [hnDens]
  rw [hneg, intervalIntegral.integral_div, ← two_mul]
  ring

lemma hnCDF_of_neg {t : ℝ} (ht : t < 0) : hnCDF t = 0 := by
  unfold hnCDF
  rw [Set.Icc_eq_empty (by linarith)]; simp

lemma hnCDF_eq_integral_max (t : ℝ) : hnCDF t = ∫ u in (0 : ℝ)..max t 0, hnDens u := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, hnCDF_eq_integral ht]
  · rw [max_eq_right ht.le, hnCDF_of_neg ht, intervalIntegral.integral_same]

lemma hnCDF_zero : hnCDF 0 = 0 := by rw [hnCDF_eq_integral le_rfl, intervalIntegral.integral_same]

lemma hnCDF_continuous : Continuous hnCDF := by
  have : hnCDF = fun t => ∫ u in (0 : ℝ)..max t 0, hnDens u := funext hnCDF_eq_integral_max
  rw [this]
  have hF : Continuous fun x => ∫ u in (0 : ℝ)..x, hnDens u :=
    intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_hnDens a b) 0
  exact hF.comp (continuous_id.max continuous_const)

lemma hnCDF_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt hnCDF (hnDens t) t := by
  have h1 : HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, hnDens u) (hnDens t) t :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_hnDens 0 t)
      hnDens_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hnDens_continuous.continuousAt
  apply h1.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with x hx
  rw [hnCDF_eq_integral hx.le]

lemma hnCDF_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    hnCDF y - hnCDF x = ∫ u in x..y, hnDens u := by
  rw [hnCDF_eq_integral hx, hnCDF_eq_integral (hx.trans hxy),
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_hnDens _ _)
      (intervalIntegrable_hnDens _ _)]

lemma hnCDF_mono : Monotone hnCDF := by
  intro x y hxy
  rcases lt_or_ge x 0 with hx | hx
  · rw [hnCDF_of_neg hx]
    unfold hnCDF; exact measureReal_nonneg
  · have := hnCDF_sub hx hxy
    have : 0 ≤ ∫ u in x..y, hnDens u :=
      intervalIntegral.integral_nonneg hxy (fun u _ => (hnDens_pos u).le)
    linarith

lemma hnCDF_nonneg (t : ℝ) : 0 ≤ hnCDF t := by unfold hnCDF; exact measureReal_nonneg

lemma hnCDF_le_one (t : ℝ) : hnCDF t ≤ 1 := by unfold hnCDF; exact measureReal_le_one

/-- `H` is Lipschitz with constant `h₀ = √(2/π)` on `[0,∞)`. -/
lemma hnCDF_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : hnCDF y - hnCDF x ≤ h0 * (y - x) := by
  rw [hnCDF_sub hx hxy]
  have := intervalIntegral.integral_mono_on hxy (intervalIntegrable_hnDens x y)
    (intervalIntegrable_const (c := h0)) (fun u _ => hnDens_le u)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

/-- `H(t) ≤ h₀ t`. -/
lemma hnCDF_le_mul (t : ℝ) (ht : 0 ≤ t) : hnCDF t ≤ h0 * t := by
  have := hnCDF_sub_le le_rfl ht
  rw [hnCDF_zero] at this; linarith

lemma hnCDF_pos {t : ℝ} (ht : 0 < t) : 0 < hnCDF t := by
  rw [hnCDF_eq_integral ht.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_hnDens 0 t)
    (fun u _ => hnDens_pos u) ht

lemma hnCDF_strictMonoOn : StrictMonoOn hnCDF (Set.Ici 0) := by
  intro x hx y _ hxy
  rw [← sub_pos, hnCDF_sub hx hxy.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_hnDens x y)
    (fun u _ => hnDens_pos u) hxy

lemma hnCDF_tendsto_one : Tendsto hnCDF atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := gaussianReal 0 1)
    (s := fun t : ℝ => Set.Icc (-t) t) (fun a b hab => Set.Icc_subset_Icc (by linarith) hab)
  have hU : (⋃ t : ℝ, Set.Icc (-t) t) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
    exact ⟨|x|, neg_abs_le x, le_abs_self x⟩
  rw [hU, measure_univ] at h
  have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  have h1 : (1 : ENNReal).toReal = 1 := by simp
  rw [h1] at this
  refine this.congr (fun t => ?_)
  rfl

lemma hnCDF_lt_one (t : ℝ) : hnCDF t < 1 := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [hnCDF_of_neg ht]; norm_num
  · have h1 : hnCDF t < hnCDF (t + 1) :=
      hnCDF_strictMonoOn ht (by simp only [Set.mem_Ici]; linarith) (by linarith)
    linarith [hnCDF_le_one (t + 1)]

/-- `H(t) = erf(t/√2)`. -/
lemma hnCDF_eq_erf {t : ℝ} (ht : 0 ≤ t) : hnCDF t = erf (t / √2) := by
  rw [hnCDF_eq_integral ht, erf]
  have h2 : (0 : ℝ) < √2 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := t / √2) hnDens h2.ne'
  rw [mul_zero, mul_div_cancel₀ _ h2.ne'] at this
  have hfun : (fun x => hnDens (√2 * x)) = fun x => h0 * exp (-x ^ 2) := by
    funext x; unfold hnDens; congr 2
    rw [mul_pow, sq_sqrt (by norm_num)]; ring
  rw [hfun, intervalIntegral.integral_const_mul, smul_eq_mul] at this
  have hval : ∫ u in (0 : ℝ)..t, hnDens u = √2 * h0 * ∫ x in (0 : ℝ)..t / √2, exp (-x ^ 2) := by
    rw [mul_assoc, this]; field_simp
  rw [hval]
  congr 1
  unfold h0
  rw [← sqrt_mul (by norm_num), show (2 : ℝ) * (2 / π) = 4 / π by ring, sqrt_div (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]

end ZeroCert

end


-- =====================================================================
-- Part: GaussProb
-- =====================================================================

section

/-!
# Probabilistic facts about standard Gaussian coefficients, and an independence tool
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- `∫_0^∞ x e^{-x²/2} dx = 1`. -/
lemma integral_Ioi_mul_exp_neg_sq_div_two :
    ∫ x in Set.Ioi (0 : ℝ), x * exp (-x ^ 2 / 2) = 1 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x => -exp (-x ^ 2 / 2))
      (x * exp (-x ^ 2 / 2)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.neg
    convert this using 1
    simp; ring
  have hlim : Tendsto (fun x : ℝ => -exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot := by
      have h := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).atTop_div_const (two_pos)
      have := tendsto_neg_atTop_atBot.comp h
      simpa [Function.comp_def, neg_div] using this
    simpa using (tendsto_exp_atBot.comp this).neg
  have hint : IntegrableOn (fun x => x * exp (-x ^ 2 / 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
      have : (0 : ℝ) < x := hx; positivity) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp

/-- A standard real Gaussian random variable. -/
def IsStdGaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Measure.map X μ = gaussianReal 0 1

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma IsStdGaussian.prob_abs_le {X : Ω → ℝ} (hX : IsStdGaussian μ X) (t : ℝ) :
    μ.real {ω | |X ω| ≤ t} = hnCDF t := by
  have : {ω | |X ω| ≤ t} = X ⁻¹' Set.Icc (-t) t := by ext ω; simp [abs_le]
  rw [this, ← map_measureReal_apply hX.1 measurableSet_Icc, hX.2]; rfl

lemma IsStdGaussian.prob_abs_lt {X : Ω → ℝ} (hX : IsStdGaussian μ X) (t : ℝ) :
    μ.real {ω | |X ω| < t} = hnCDF t := by
  have : {ω | |X ω| < t} = X ⁻¹' Set.Ioo (-t) t := by ext ω; simp [abs_lt]
  rw [this, ← map_measureReal_apply hX.1 measurableSet_Ioo, hX.2]
  unfold hnCDF
  exact measureReal_congr (Ioo_ae_eq_Icc' (ZeroCert.zc_gauss_singleton _) (ZeroCert.zc_gauss_singleton _))

lemma IsStdGaussian.prob_norm_le {X : Ω → ℝ} (hX : IsStdGaussian μ X) (t : ℝ) :
    μ.real {ω | ‖(X ω : ℂ)‖ ≤ t} = hnCDF t := by
  simp only [Complex.norm_real, Real.norm_eq_abs]; exact hX.prob_abs_le μ t

lemma IsStdGaussian.ae_ne_zero {X : Ω → ℝ} (hX : IsStdGaussian μ X) : ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  have h0 : μ (X ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hX.1 (measurableSet_singleton 0), hX.2]
    exact ZeroCert.zc_gauss_singleton 0
  rw [ae_iff]
  convert h0 using 2
  ext ω
  simp

lemma IsStdGaussian.integrable_abs {X : Ω → ℝ} (hX : IsStdGaussian μ X) :
    Integrable (fun ω => |X ω|) μ := by
  have h1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).abs
  rw [← hX.2] at h1
  exact (integrable_map_measure h1.aestronglyMeasurable hX.1.aemeasurable).mp h1

/-- `𝔼|X| = √(2/π)` for a standard Gaussian `X`. -/
lemma IsStdGaussian.integral_abs {X : Ω → ℝ} (hX : IsStdGaussian μ X) :
    ∫ ω, |X ω| ∂μ = h0 := by
  have : ∫ ω, |X ω| ∂μ = ∫ x, |x| ∂(gaussianReal 0 1) := by
    rw [← hX.2, integral_map hX.1.aemeasurable (continuous_abs.aestronglyMeasurable)]
  rw [this, integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, gaussianPDFReal_std]
  have h := integral_comp_abs (f := fun y => hnDens y / 2 * y)
  have hfun : (fun x : ℝ => hnDens x / 2 * |x|) = fun x => hnDens |x| / 2 * |x| := by
    funext x; unfold hnDens; rw [sq_abs]
  rw [hfun, h]
  have : ∫ x in Set.Ioi (0 : ℝ), hnDens x / 2 * x =
      h0 / 2 * ∫ x in Set.Ioi (0 : ℝ), x * exp (-x ^ 2 / 2) := by
    rw [← integral_const_mul]
    congr 1; funext x; unfold hnDens; ring
  rw [this, integral_Ioi_mul_exp_neg_sq_div_two]
  ring

/-! ### Independence tool -/

/-- For independent `T` and `W`, `ℙ{(T, W) ∈ S} = 𝔼[ℙ{(T, w) ∈ S}|_{w = W}]`. -/
lemma indep_measureReal_eq_integral [IsProbabilityMeasure μ] {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ]
    (T : Ω → β) (W : Ω → γ) (hT : Measurable T) (hW : Measurable W) (hind : IndepFun T W μ)
    (S : Set (β × γ)) (hS : MeasurableSet S) :
    μ.real {ω | (T ω, W ω) ∈ S} = ∫ ω, μ.real {ω' | (T ω', W ω) ∈ S} ∂μ := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hW.aemeasurable).mp hind
  have h1 : μ {ω | (T ω, W ω) ∈ S} =
      ∫⁻ w, (μ.map T) {x | (x, w) ∈ S} ∂(μ.map W) := by
    have : {ω | (T ω, W ω) ∈ S} = (fun ω => (T ω, W ω)) ⁻¹' S := rfl
    rw [this, ← Measure.map_apply (hT.prodMk hW) hS, hmap, Measure.prod_apply_symm hS]
    rfl
  have hmeas : Measurable fun w => (μ.map T) {x | (x, w) ∈ S} :=
    measurable_measure_prodMk_right hS
  rw [lintegral_map hmeas hW] at h1
  have h2 : ∀ ω, (μ.map T) {x | (x, W ω) ∈ S} = μ {ω' | (T ω', W ω) ∈ S} := by
    intro ω
    rw [Measure.map_apply hT]
    · rfl
    · exact measurable_prodMk_right hS
  simp_rw [h2] at h1
  rw [Measure.real, h1, ← integral_toReal]
  · rfl
  · exact (hmeas.comp hW).aemeasurable.congr (ae_of_all _ (fun ω => h2 ω))
  · exact ae_of_all _ (fun ω => measure_lt_top μ _)

end ZeroCert

end


-- =====================================================================
-- Part: GaussPoly
-- =====================================================================

section

/-!
# Real Gaussian polynomials: setup, and the Gaussian corollaries of Section 3
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped Pointwise

namespace ZeroCert

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Complex coefficients obtained from real ones. -/
noncomputable def realCoeff (X : ℕ → Ω → ℝ) : ℕ → Ω → ℂ := fun k ω => (X k ω : ℂ)

/-- `X_0, …, X_{m-1}` are iid standard real Gaussian variables. -/
structure IidStdGaussian (m : ℕ) (X : ℕ → Ω → ℝ) : Prop where
  gauss : ∀ k < m, IsStdGaussian μ (X k)
  indep : iIndepFun (fun k : Fin m => X k) μ

variable {μ}

lemma IidStdGaussian.measurable {m : ℕ} {X : ℕ → Ω → ℝ} (h : IidStdGaussian μ m X) {k : ℕ}
    (hk : k < m) : Measurable (X k) := (h.gauss k hk).1

/-- The first `n` of `n + 1` iid Gaussians are iid. -/
lemma IidStdGaussian.init {n : ℕ} {X : ℕ → Ω → ℝ} (h : IidStdGaussian μ (n + 1) X) :
    IidStdGaussian μ n X where
  gauss k hk := h.gauss k (by omega)
  indep := by
    have := h.indep.precomp (g := Fin.castSucc) (Fin.castSucc_injective n)
    exact this

/-- `(X_0, …, X_{n-1})` is independent of `X_n`. -/
lemma IidStdGaussian.indep_init_last {n : ℕ} {X : ℕ → Ω → ℝ} (h : IidStdGaussian μ (n + 1) X) :
    IndepFun (fun ω (k : Fin n) => X k ω) (X n) μ := by
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => i ≠ Fin.last n)
  set T : Finset (Fin (n + 1)) := {Fin.last n}
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]; intro i hi hiT
    simp only [S, Finset.mem_filter] at hi
    exact hi.2 (Finset.mem_singleton.mp hiT)
  have hmeas : ∀ i : Fin (n + 1), Measurable (X i) := fun i => h.measurable i.2
  have hST := h.indep.indepFun_finset S T hdisj hmeas
  set φ : (S → ℝ) → (Fin n → ℝ) := fun g k =>
    g ⟨k.castSucc, by simp [S, Fin.castSucc_ne_last]⟩
  set ψ : (T → ℝ) → ℝ := fun g => g ⟨Fin.last n, Finset.mem_singleton_self _⟩
  have hφ : Measurable φ := zc_measurable_pi (fun k => measurable_pi_apply _)
  have hψ : Measurable ψ := measurable_pi_apply _
  have := hST.comp hφ hψ
  exact this

lemma IidStdGaussian.ae_ne_zero {m : ℕ} {X : ℕ → Ω → ℝ} (h : IidStdGaussian μ m X) {k : ℕ}
    (hk : k < m) : ∀ᵐ ω ∂μ, X k ω ≠ 0 := (h.gauss k hk).ae_ne_zero μ

/-- Independence gives a product formula for box events (real-valued version). -/
lemma prob_forall_fin_eq_prod_real (n : ℕ) (Y : ℕ → Ω → ℝ)
    (hind : iIndepFun (fun (k : Fin n) => Y k) μ) (S : ℕ → Set ℝ)
    (hS : ∀ k, MeasurableSet (S k)) :
    μ.real {ω | ∀ k < n, Y k ω ∈ S k} = ∏ k ∈ range n, μ.real {ω | Y k ω ∈ S k} := by
  have h := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun k => S k)
    (fun k _ => hS k)
  have hset : {ω | ∀ k < n, Y k ω ∈ S k} = ⋂ i ∈ (Finset.univ : Finset (Fin n)),
      (fun (k : Fin n) => Y k) i ⁻¹' S i := by
    ext ω; simp only [ZeroCert.zc_mem_setOf_eq, Finset.mem_univ, Set.iInter_true, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩
  rw [Measure.real, hset, h, ENNReal.toReal_prod,
    Finset.prod_range (fun k => μ.real {ω | Y k ω ∈ S k})]
  rfl

/-- For iid standard Gaussians, `ℙ{|X_k| ≤ t ∀ k < n} = H(t)^n`. -/
lemma IidStdGaussian.prob_all_abs_le [IsProbabilityMeasure μ] {n : ℕ} {X : ℕ → Ω → ℝ}
    (h : IidStdGaussian μ n X) (t : ℝ) :
    μ.real {ω | ∀ k < n, |X k ω| ≤ t} = hnCDF t ^ n := by
  have := prob_forall_fin_eq_prod_real n X h.indep (fun _ => Set.Icc (-t) t)
    (fun _ => measurableSet_Icc)
  simp only [Set.mem_Icc, ← abs_le] at this
  rw [this, Finset.prod_congr rfl (fun k hk => (h.gauss k (Finset.mem_range.mp hk)).prob_abs_le μ t)]
  simp

lemma iIndepFun_ofReal {n : ℕ} {X : ℕ → Ω → ℝ} (h : iIndepFun (fun k : Fin n => X k) μ) :
    iIndepFun (fun k : Fin n => fun ω => (X k ω : ℂ)) μ :=
  h.comp (fun _ x => (x : ℂ)) (fun _ => Complex.measurable_ofReal)

variable (μ) [IsProbabilityMeasure μ]

/-- **Corollary 3.2 (Gaussian monic Cauchy certificate), lower bound.**
`[erf((c-1)/√2)]^n ≤ Π_{P_n}(c)` for `c ≥ 1`. -/
theorem gauss_monic_lower (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ n X)
    (c : ℝ) (hc : 1 ≤ c) :
    erf ((c - 1) / √2) ^ n ≤ containProb μ n (monicCoeff n (realCoeff X)) c := by
  have := monic_cauchy_certificate μ hC n (realCoeff X) (iIndepFun_ofReal hX.indep) hnCDF
    (fun k hk t => (hX.gauss k hk).prob_norm_le μ t) c
  rwa [hnCDF_eq_erf (by linarith)] at this

/-- **Corollary 3.2, upper bound** (Vieta): `Π_{P_n}(c) ≤ erf(c^n/√2)` for `c ≥ 0`. -/
theorem gauss_monic_upper (hV : VietaBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ n X) (c : ℝ) (hc : 0 ≤ c) :
    containProb μ n (monicCoeff n (realCoeff X)) c ≤ erf (c ^ n / √2) := by
  have h := vieta_lower_certificate μ hV n hn (monicCoeff n (realCoeff X))
    (monicCoeff_self n _) c hc
  have h0 : ∀ ω, monicCoeff n (realCoeff X) 0 ω = (X 0 ω : ℂ) := fun ω => by
    rw [monicCoeff_of_lt n _ ω (by omega)]; rfl
  simp_rw [h0] at h
  rwa [(hX.gauss 0 (by omega)).prob_norm_le μ, hnCDF_eq_erf (by positivity)] at h

/-- The inverse error function on `[0,1)`: `erf⁻¹(u) = inf {x ≥ 0 : erf x ≥ u}`. -/
noncomputable def erfInv (u : ℝ) : ℝ := lowerQuantile erf u

lemma lowerQuantile_hnCDF (u : ℝ) : lowerQuantile hnCDF u = √2 * erfInv u := by
  unfold erfInv lowerQuantile
  have h2 : (0 : ℝ) < √2 := by positivity
  have hset : {t | 0 ≤ t ∧ u ≤ hnCDF t} = √2 • {x | 0 ≤ x ∧ u ≤ erf x} := by
    ext t
    simp only [ZeroCert.zc_mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨ht, hu⟩
      refine ⟨t / √2, ⟨by positivity, by rwa [← hnCDF_eq_erf ht]⟩, by field_simp⟩
    · rintro ⟨x, ⟨hx, hu⟩, rfl⟩
      refine ⟨by positivity, ?_⟩
      rw [hnCDF_eq_erf (by positivity), mul_div_cancel_left₀ _ h2.ne']
      exact hu
  rw [hset, Real.sInf_smul_of_nonneg h2.le, smul_eq_mul]

/-- **Corollary 3.2, radius.** `c_p = 1 + √2 erf⁻¹(p^{1/n})` is a certified confidence radius. -/
theorem gauss_monic_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ n X) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsProbZeroBound μ n (monicCoeff n (realCoeff X)) (1 + √2 * erfInv (p ^ (1 / (n : ℝ)))) p := by
  have h := monic_cauchy_radius μ hC n hn (realCoeff X)
    (Complex.measurable_ofReal.comp ((hX.gauss 0 (by omega)).1))
    (iIndepFun_ofReal hX.indep) (fun k hk t =>
      ((hX.gauss k hk).prob_norm_le μ t).trans ((hX.gauss 0 (by omega)).prob_norm_le μ t).symm)
      p hp0 hp1
  have hfun : (fun t => μ.real {ω | ‖realCoeff X 0 ω‖ ≤ t}) = hnCDF := by
    funext t; exact (hX.gauss 0 (by omega)).prob_norm_le μ t
  rwa [hfun, lowerQuantile_hnCDF] at h

/-- **Corollary 3.6, Gaussian case.** `Π_{P_n}(c) ≥ ∏_{j=1}^n erf((c/2)^j/√2)`. -/
theorem gauss_fujiwara_certificate (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ n X) (c : ℝ) (hc : 0 < c) :
    ∏ j ∈ Finset.Icc 1 n, erf ((c / 2) ^ j / √2) ≤
      containProb μ n (monicCoeff n (realCoeff X)) c := by
  have := fujiwara_certificate μ hC n (realCoeff X) (iIndepFun_ofReal hX.indep) hnCDF
    (fun k hk t => (hX.gauss k hk).prob_norm_le μ t) c hc
  rwa [Finset.prod_congr rfl (fun j _ => hnCDF_eq_erf (by positivity))] at this

end ZeroCert

end


-- =====================================================================
-- Part: Ratios
-- =====================================================================

section

/-!
# Section 4: Gaussian ratios with a common denominator
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- The exact law of the ratio maximum,
`I_n(r) = √(2/π) ∫_0^∞ e^{-x²/2} [erf(r x/√2)]^n dx`. -/
noncomputable def ratioLaw (n : ℕ) (r : ℝ) : ℝ :=
  √(2 / π) * ∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 2 / 2) * erf (r * x / √2) ^ n

/-- `I_n^{-1}(p) = inf {r ≥ 0 : I_n(r) ≥ p}`. -/
noncomputable def ratioLawInv (n : ℕ) (p : ℝ) : ℝ := lowerQuantile (ratioLaw n) p

/-- The same law written with the half-normal distribution function, for every real `r`. -/
noncomputable def ratioJ (n : ℕ) (r : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), hnDens x * hnCDF (r * x) ^ n

lemma ratioLaw_eq_ratioJ (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : ratioLaw n r = ratioJ n r := by
  unfold ratioLaw ratioJ
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx : 0 < x := hx
  rw [hnCDF_eq_erf (by positivity)]
  unfold hnDens h0; ring

lemma integrable_hnDens : Integrable hnDens := by
  have : hnDens = fun x => 2 * gaussianPDFReal 0 1 x := by
    funext x; rw [gaussianPDFReal_std]; ring
  rw [this]; exact (integrable_gaussianPDFReal 0 1).const_mul 2

lemma integral_Ioi_hnDens : ∫ x in Set.Ioi (0 : ℝ), hnDens x = 1 := by
  have h1 : ∫ x, gaussianPDFReal 0 1 x = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have h2 : ∫ x, hnDens |x| / 2 = 2 * ∫ x in Set.Ioi 0, hnDens x / 2 :=
    integral_comp_abs (f := fun y => hnDens y / 2)
  have hfun : (fun x => hnDens |x| / 2) = gaussianPDFReal 0 1 := by
    funext x; rw [gaussianPDFReal_std]; unfold hnDens; rw [sq_abs]
  rw [hfun, h1, integral_div] at h2
  linarith

lemma ratioJ_integrand_le (n : ℕ) (r x : ℝ) : ‖hnDens x * hnCDF (r * x) ^ n‖ ≤ hnDens x := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnDens_pos x).le
    (pow_nonneg (hnCDF_nonneg _) _))]
  have : hnCDF (r * x) ^ n ≤ 1 := pow_le_one₀ (hnCDF_nonneg _) (hnCDF_le_one _)
  have := hnDens_pos x
  nlinarith

lemma ratioJ_integrand_continuous (n : ℕ) (t : ℝ) :
    Continuous fun x => hnDens x * hnCDF (t * x) ^ n :=
  hnDens_continuous.mul ((hnCDF_continuous.comp (continuous_const.mul continuous_id)).pow n)

lemma ratioJ_integrableOn (n : ℕ) (t : ℝ) :
    IntegrableOn (fun x => hnDens x * hnCDF (t * x) ^ n) (Set.Ioi 0) :=
  (Integrable.mono' integrable_hnDens (ratioJ_integrand_continuous n t).aestronglyMeasurable
    (ae_of_all _ (fun x => ratioJ_integrand_le n t x))).integrableOn

lemma ratioJ_continuous (n : ℕ) : Continuous (ratioJ n) := by
  unfold ratioJ
  apply continuous_of_dominated (bound := hnDens)
  · intro r
    exact (hnDens_continuous.mul ((hnCDF_continuous.comp
      (continuous_const.mul continuous_id)).pow n)).aestronglyMeasurable
  · intro r; exact ae_of_all _ (fun x => ratioJ_integrand_le n r x)
  · exact integrable_hnDens.integrableOn
  · exact ae_of_all _ (fun x => by
      have : Continuous fun r : ℝ => hnCDF (r * x) :=
        hnCDF_continuous.comp (continuous_id.mul continuous_const)
      exact continuous_const.mul (this.pow n))

lemma ratioJ_zero (n : ℕ) (hn : 1 ≤ n) : ratioJ n 0 = 0 := by
  unfold ratioJ
  simp [hnCDF_zero, zero_pow (by omega : n ≠ 0)]

lemma ratioJ_tendsto_one (n : ℕ) : Tendsto (ratioJ n) atTop (𝓝 1) := by
  rw [← integral_Ioi_hnDens]
  unfold ratioJ
  apply tendsto_integral_filter_of_dominated_convergence (bound := hnDens)
  · exact Eventually.of_forall (fun r => (hnDens_continuous.mul ((hnCDF_continuous.comp
      (continuous_const.mul continuous_id)).pow n)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun r => ae_of_all _ (fun x => ratioJ_integrand_le n r x))
  · exact integrable_hnDens.integrableOn
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun x hx => ?_)
    have hx : 0 < x := hx
    have : Tendsto (fun r : ℝ => hnCDF (r * x)) atTop (𝓝 1) :=
      hnCDF_tendsto_one.comp (tendsto_id.atTop_mul_const hx)
    simpa using (this.pow n).const_mul (hnDens x)

lemma ratioJ_mono (n : ℕ) : Monotone (ratioJ n) := by
  intro r s hrs
  unfold ratioJ
  apply setIntegral_mono_on
  · exact ratioJ_integrableOn n r
  · exact ratioJ_integrableOn n s
  · exact measurableSet_Ioi
  · intro x hx
    have hx : 0 < x := hx
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hnCDF_nonneg _)
      (hnCDF_mono (by nlinarith)) n) (hnDens_pos x).le

lemma ratioJ_strictMonoOn (n : ℕ) (hn : 1 ≤ n) : StrictMonoOn (ratioJ n) (Set.Ici 0) := by
  intro r hr s _ hrs
  have hr : 0 ≤ r := hr
  unfold ratioJ
  have hint : ∀ t, IntegrableOn (fun x => hnDens x * hnCDF (t * x) ^ n) (Set.Ioi 0) :=
    ratioJ_integrableOn n
  rw [← sub_pos, ← integral_sub (hint s) (hint r)]
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 < hnDens x * hnCDF (s * x) ^ n - hnDens x * hnCDF (r * x) ^ n := by
    intro x hx
    have hx : 0 < x := hx
    rw [sub_pos]
    apply mul_lt_mul_of_pos_left _ (hnDens_pos x)
    apply pow_lt_pow_left₀ _ (hnCDF_nonneg _) (by omega)
    exact hnCDF_strictMonoOn (by simp only [Set.mem_Ici]; positivity)
      (by simp only [Set.mem_Ici]; nlinarith) (by nlinarith)
  have hcont : ContinuousOn (fun x => hnDens x * hnCDF (s * x) ^ n -
      hnDens x * hnCDF (r * x) ^ n) (Set.Ioi 0) := by
    apply Continuous.continuousOn
    exact (hnDens_continuous.mul ((hnCDF_continuous.comp
      (continuous_const.mul continuous_id)).pow n)).sub
      (hnDens_continuous.mul ((hnCDF_continuous.comp
      (continuous_const.mul continuous_id)).pow n))
  have := setIntegral_pos_iff_support_of_nonneg_ae (μ := volume) (s := Set.Ioi (0 : ℝ))
    (f := fun x => hnDens x * hnCDF (s * x) ^ n - hnDens x * hnCDF (r * x) ^ n)
    (by rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact ae_of_all _ (fun x hx => (hpos x hx).le))
    ((hint s).sub (hint r))
  rw [this]
  have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun x => hnDens x * hnCDF (s * x) ^ n -
      hnDens x * hnCDF (r * x) ^ n) := fun x hx => (hpos x hx).ne'
  calc (0 : ENNReal) < volume (Set.Ioi (0 : ℝ)) := by simp
    _ = volume (Function.support (fun x => hnDens x * hnCDF (s * x) ^ n -
        hnDens x * hnCDF (r * x) ^ n) ∩ Set.Ioi 0) := by
        rw [Set.inter_eq_right.mpr hsub]

/-! ### The exact common-denominator law -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Theorem 4.1 (Exact common-denominator certificate), distribution.**
`ℙ{max_{k<n} |X_k/X_n| ≤ r} = I_n(r)` for `r ≥ 0`. -/
theorem ratio_law (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (r : ℝ)
    (hr : 0 ≤ r) :
    μ.real {ω | ∀ k < n, |X k ω / X n ω| ≤ r} = ratioLaw n r := by
  have hXn : IsStdGaussian μ (X n) := hX.gauss n (by omega)
  -- remove the null event `X_n = 0`
  have hae : {ω | ∀ k < n, |X k ω / X n ω| ≤ r} =ᵐ[μ] {ω | ∀ k < n, |X k ω| ≤ r * |X n ω|} := by
    filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω
    have hpos : 0 < |X n ω| := abs_pos.mpr hω
    apply propext
    show (∀ k < n, |X k ω / X n ω| ≤ r) ↔ (∀ k < n, |X k ω| ≤ r * |X n ω|)
    simp only [abs_div, div_le_iff₀ hpos]
  rw [measureReal_congr hae]
  set V : Ω → (Fin n → ℝ) := fun ω k => X k ω
  set S : Set ((Fin n → ℝ) × ℝ) := {p | ∀ k, |p.1 k| ≤ r * |p.2|}
  have hS : MeasurableSet S := by
    have : S = ⋂ k : Fin n, {p : (Fin n → ℝ) × ℝ | |p.1 k| ≤ r * |p.2|} := by
      ext p; simp [S]
    rw [this]
    exact MeasurableSet.iInter (fun k => measurableSet_le
      ((measurable_pi_apply k).comp measurable_fst).abs
      (measurable_const.mul measurable_snd.abs))
  have hVm : Measurable V := zc_measurable_pi (fun k => hX.measurable (by omega))
  have hset : {ω | ∀ k < n, |X k ω| ≤ r * |X n ω|} = {ω | (V ω, X n ω) ∈ S} := by
    ext ω; simp only [ZeroCert.zc_mem_setOf_eq, S, V]
    exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩
  rw [hset, indep_measureReal_eq_integral μ V (X n) hVm hXn.1 hX.indep_init_last S hS]
  have hinner : ∀ ω, μ.real {ω' | (V ω', X n ω) ∈ S} = hnCDF (r * |X n ω|) ^ n := by
    intro ω
    rw [← hX.init.prob_all_abs_le (r * |X n ω|)]
    congr 1; ext ω'; simp only [ZeroCert.zc_mem_setOf_eq, S, V]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩
  simp_rw [hinner]
  have hmap : ∫ ω, hnCDF (r * |X n ω|) ^ n ∂μ = ∫ x, hnCDF (r * |x|) ^ n ∂(gaussianReal 0 1) := by
    rw [← hXn.2, integral_map hXn.1.aemeasurable]
    exact ((hnCDF_continuous.comp (continuous_const.mul continuous_abs)).pow n).aestronglyMeasurable
  rw [hmap, integral_gaussianReal_eq_integral_smul one_ne_zero, ratioLaw_eq_ratioJ n hr]
  simp only [smul_eq_mul, gaussianPDFReal_std]
  have h := integral_comp_abs (f := fun y => hnDens y / 2 * hnCDF (r * y) ^ n)
  have hfun : (fun x : ℝ => hnDens x / 2 * hnCDF (r * |x|) ^ n) =
      fun x => hnDens |x| / 2 * hnCDF (r * |x|) ^ n := by
    funext x; unfold hnDens; rw [sq_abs]
  rw [hfun, h, ratioJ, ← integral_const_mul]
  congr 1; funext x; ring

/-- Dividing all coefficients by the leading one does not change the zeros. -/
lemma zerosWithin_of_normalized (n : ℕ) (a : ℕ → ℂ) (c : ℝ)
    (h : ZerosWithin n (fun k => a k / a n) c) : ZerosWithin n a c := by
  intro z hz
  apply h z
  unfold peval at hz ⊢
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hz, zero_div]

/-- **Theorem 4.1, certificate.** `Π_{Q_n}(c) ≥ I_n(c-1)` for `c ≥ 1`. -/
theorem ratio_certificate (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (c : ℝ) (hc : 1 ≤ c) :
    ratioLaw n (c - 1) ≤ containProb μ n (realCoeff X) c := by
  rw [← ratio_law μ n X hX (c - 1) (by linarith)]
  apply measureReal_mono_ae'
  filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω hall
  apply zerosWithin_of_normalized n _
  have := hC n (fun k => realCoeff X k ω / realCoeff X n ω) (c - 1)
    (by simp [realCoeff, hω]) (fun k hk => by
      simp only [realCoeff, norm_div, Complex.norm_real, Real.norm_eq_abs, ← abs_div]
      exact hall k hk)
  simpa using this

/-- **Corollary 4.2 (Certified confidence radius) — analytic facts.** For `n ≥ 1`, `I_n` is
continuous, `I_n(0) = 0`, `I_n(r) → 1`, and `I_n` is strictly increasing on `[0, ∞)`, so for
`0 < p < 1` the equation `I_n(r) = p` has a unique solution `r ≥ 0`, namely `I_n^{-1}(p)`. -/
theorem ratioLaw_properties (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (ratioLaw n) (Set.Ici 0) ∧ ratioLaw n 0 = 0 ∧
    Tendsto (ratioLaw n) atTop (𝓝 1) ∧ StrictMonoOn (ratioLaw n) (Set.Ici 0) ∧
    ∀ p, 0 < p → p < 1 → 0 ≤ ratioLawInv n p ∧ ratioLaw n (ratioLawInv n p) = p ∧
      ∀ r, 0 ≤ r → ratioLaw n r = p → r = ratioLawInv n p := by
  have heq : Set.EqOn (ratioLaw n) (ratioJ n) (Set.Ici 0) := fun r hr => ratioLaw_eq_ratioJ n hr
  have hcont : ContinuousOn (ratioLaw n) (Set.Ici 0) :=
    (ratioJ_continuous n).continuousOn.congr heq
  have hlim : Tendsto (ratioLaw n) atTop (𝓝 1) := by
    apply (ratioJ_tendsto_one n).congr'
    filter_upwards [eventually_ge_atTop 0] with r hr using (heq hr).symm
  have hsm : StrictMonoOn (ratioLaw n) (Set.Ici 0) := fun r hr s hs hrs => by
    rw [heq hr, heq hs]; exact ratioJ_strictMonoOn n hn hr hs hrs
  refine ⟨hcont, by rw [heq (Set.mem_Ici.mpr le_rfl), ratioJ_zero n hn], hlim, hsm, ?_⟩
  intro p hp0 hp1
  -- existence of a solution by the intermediate value theorem
  obtain ⟨R, hR⟩ := (hlim.eventually (Ioi_mem_nhds hp1)).exists_forall_of_atTop
  set R' := max R 0
  have hR' : p < ratioLaw n R' := hR R' (le_max_left _ _)
  have h0 : ratioLaw n 0 = 0 := by rw [heq (Set.mem_Ici.mpr le_rfl), ratioJ_zero n hn]
  obtain ⟨r0, hr0, hr0p⟩ := intermediate_value_Icc (le_max_right R 0)
    (hcont.mono (Set.Icc_subset_Ici_self)) ⟨by rw [h0]; exact hp0.le, hR'.le⟩
  have hr0' : 0 ≤ r0 := hr0.1
  have huniq : ∀ r, 0 ≤ r → ratioLaw n r = p → r = r0 := by
    intro r hr hrp
    rcases lt_trichotomy r r0 with h | h | h
    · have := hsm hr hr0' h; linarith
    · exact h
    · have := hsm hr0' hr h; linarith
  have hq : ratioLawInv n p = r0 := by
    unfold ratioLawInv lowerQuantile
    have hset : {t | 0 ≤ t ∧ p ≤ ratioLaw n t} = Set.Ici r0 := by
      ext t; simp only [ZeroCert.zc_mem_setOf_eq, Set.mem_Ici]
      constructor
      · rintro ⟨ht, htp⟩
        by_contra hlt; push Not at hlt
        have := hsm ht hr0' hlt; linarith
      · intro ht
        refine ⟨hr0'.trans ht, ?_⟩
        rcases ht.lt_or_eq with h | h
        · have := hsm hr0' (hr0'.trans h.le) h; linarith
        · rw [← h, hr0p]
    rw [hset, csInf_Ici]
  rw [hq]
  exact ⟨hr0', hr0p, huniq⟩

/-- **Corollary 4.2 (Certified confidence radius).** `c_{n,p} = 1 + I_n^{-1}(p)` is a
probabilistic zero bound for `Q_n` at confidence `p`. -/
theorem ratio_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsProbZeroBound μ n (realCoeff X) (1 + ratioLawInv n p) p := by
  obtain ⟨-, -, -, -, h⟩ := ratioLaw_properties n hn
  obtain ⟨hq0, hqp, -⟩ := h p hp0 hp1
  have := ratio_certificate μ hC n X hX (1 + ratioLawInv n p) (by linarith)
  rw [add_sub_cancel_left, hqp] at this
  exact this

end ZeroCert

end


-- =====================================================================
-- Part: CauchyLaw
-- =====================================================================

section

/-!
# The Cauchy law of a Gaussian ratio, and the remaining results of Section 4
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- `∫_0^∞ x e^{-c x²/2} dx = 1/c` for `c > 0`. -/
lemma integral_Ioi_mul_exp_neg_mul_sq_div_two {c : ℝ} (hc : 0 < c) :
    ∫ x in Set.Ioi (0 : ℝ), x * exp (-(c * x ^ 2) / 2) = 1 / c := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x => -exp (-(c * x ^ 2) / 2) / c)
      (x * exp (-(c * x ^ 2) / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(c * x ^ 2) / 2) (-(c * x)) x := by
      have := ((hasDerivAt_pow 2 x).const_mul c).neg.div_const 2
      convert this using 1; push_cast; ring
    have h2 := (h1.exp.neg).div_const c
    convert h2 using 1
    field_simp
  have hlim : Tendsto (fun x : ℝ => -exp (-(c * x ^ 2) / 2) / c) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -(c * x ^ 2) / 2) atTop atBot := by
      have h := ((tendsto_pow_atTop (α := ℝ) (two_ne_zero)).const_mul_atTop hc).atTop_div_const
        (two_pos)
      have := tendsto_neg_atTop_atBot.comp h
      simpa [Function.comp_def, neg_div] using this
    simpa using ((tendsto_exp_atBot.comp this).neg).div_const c
  have hint : IntegrableOn (fun x => x * exp (-(c * x ^ 2) / 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
      have : (0 : ℝ) < x := hx; positivity) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp; ring

lemma integrableOn_mul_hnDens : IntegrableOn (fun x => x * hnDens x) (Set.Ioi 0) := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x => -exp (-x ^ 2 / 2))
      (x * exp (-x ^ 2 / 2)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.neg
    convert this using 1
    simp; ring
  have hlim : Tendsto (fun x : ℝ => -exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -x ^ 2 / 2) atTop atBot := by
      have h := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).atTop_div_const (two_pos)
      have := tendsto_neg_atTop_atBot.comp h
      simpa [Function.comp_def, neg_div] using this
    simpa using (tendsto_exp_atBot.comp this).neg
  have hint : IntegrableOn (fun x => x * exp (-x ^ 2 / 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
      have : (0 : ℝ) < x := hx; positivity) hlim
  have : IntegrableOn (fun x => h0 * (x * exp (-x ^ 2 / 2))) (Set.Ioi 0) := hint.const_mul h0
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold hnDens; ring

/-- Derivative of `I_1` at `r > 0`. -/
lemma ratioJ_one_hasDerivAt {r0 : ℝ} (hr0 : 0 < r0) :
    HasDerivAt (ratioJ 1) (2 / π * (1 / (1 + r0 ^ 2))) r0 := by
  set F : ℝ → ℝ → ℝ := fun r x => hnDens x * hnCDF (r * x)
  set F' : ℝ → ℝ → ℝ := fun r x => hnDens x * (hnDens (r * x) * x)
  have hs : Set.Ioi (r0 / 2) ∈ 𝓝 r0 := Ioi_mem_nhds (by linarith)
  have hF_meas : ∀ᶠ r in 𝓝 r0, AEStronglyMeasurable (F r) (volume.restrict (Set.Ioi 0)) :=
    Eventually.of_forall (fun r => by
      have := (ratioJ_integrand_continuous 1 r).aestronglyMeasurable
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      simpa [F] using this)
  have hF_int : Integrable (F r0) (volume.restrict (Set.Ioi 0)) := by
    have := ratioJ_integrableOn 1 r0
    simp only [pow_one] at this
    exact this
  have hF'_cont : ∀ r, Continuous (F' r) := fun r => by
    simp only [F']
    exact hnDens_continuous.mul ((hnDens_continuous.comp (continuous_const.mul continuous_id)).mul
      continuous_id)
  have h_bound : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ r ∈ Set.Ioi (r0 / 2),
      ‖F' r x‖ ≤ h0 * (x * hnDens x) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun x hx r _ => ?_)
    have hx : 0 < x := hx
    simp only [F', Real.norm_eq_abs]
    rw [abs_of_nonneg (by have := hnDens_pos x; have := hnDens_pos (r * x); positivity)]
    have h1 := hnDens_le (r * x)
    have h2 := hnDens_pos x
    nlinarith [mul_pos h2 hx]
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ r ∈ Set.Ioi (r0 / 2),
      HasDerivAt (fun r => F r x) (F' r x) r := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun x hx r hr => ?_)
    have hx : 0 < x := hx
    have hr : 0 < r := lt_trans (by linarith) (Set.mem_Ioi.mp hr)
    have h := (hnCDF_hasDerivAt (mul_pos hr hx)).comp r ((hasDerivAt_id r).mul_const x)
    simp only [F, F']
    simpa [mul_comm] using h.const_mul (hnDens x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int
    ((hF'_cont r0).aestronglyMeasurable) h_bound (integrableOn_mul_hnDens.const_mul h0) h_diff
  have hval : ∫ x in Set.Ioi (0 : ℝ), F' r0 x = 2 / π * (1 / (1 + r0 ^ 2)) := by
    have : ∀ x, F' r0 x = h0 ^ 2 * (x * exp (-((1 + r0 ^ 2) * x ^ 2) / 2)) := by
      intro x; simp only [F', hnDens]
      rw [show -(r0 * x) ^ 2 / 2 = -(r0 ^ 2 * x ^ 2) / 2 by ring]
      rw [show -((1 + r0 ^ 2) * x ^ 2) / 2 = -x ^ 2 / 2 + -(r0 ^ 2 * x ^ 2) / 2 by ring, exp_add]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq_div_two (by positivity), h0_sq]
  rw [← hval]
  convert key.2 using 1
  funext r; simp [ratioJ, F]

/-- **The Cauchy law** in the form `I_1(r) = (2/π) arctan r` for `r ≥ 0`
(this is the first identity of Remark 4.5). -/
theorem ratioLaw_one {r : ℝ} (hr : 0 ≤ r) : ratioLaw 1 r = 2 / π * arctan r := by
  rw [ratioLaw_eq_ratioJ 1 hr]
  set G : ℝ → ℝ := fun r => ratioJ 1 r - 2 / π * arctan r
  have hGc : Continuous G := (ratioJ_continuous 1).sub (continuous_const.mul continuous_arctan)
  have hG0 : G 0 = 0 := by simp [G, ratioJ_zero 1 le_rfl]
  have hderiv : ∀ x, 0 < x → HasDerivAt G 0 x := by
    intro x hx
    have h1 := ratioJ_one_hasDerivAt hx
    have h2 := (hasDerivAt_arctan x).const_mul (2 / π)
    have h3 : HasDerivAt G (_ - _) x := h1.sub h2
    simpa using h3
  suffices G r = 0 by simp only [G] at this; linarith
  rcases hr.lt_or_eq with hr | hr
  · have hconst : ∀ ε ∈ Set.Ioo (0 : ℝ) r, G r = G ε := by
      intro ε hε
      exact constant_of_has_deriv_right_zero hGc.continuousOn
        (fun x hx => (hderiv x (lt_of_lt_of_le hε.1 hx.1)).hasDerivWithinAt) r
        ⟨hε.2.le, le_rfl⟩
    have hlim : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) := hGc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε = G r := by
      filter_upwards [Ioo_mem_nhdsGT hr] with ε hε using (hconst ε hε).symm
    have : Tendsto G (𝓝[>] 0) (𝓝 (G r)) := tendsto_const_nhds.congr' (EventuallyEq.symm hev)
    rw [← hG0]; exact tendsto_nhds_unique this hlim
  · rw [← hr, hG0]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Cauchy law of Gaussian ratios.** For iid standard Gaussians, each ratio `X_j/X_k`
(`j ≠ k`) is standard Cauchy: `ℙ{|X_j/X_k| ≤ r} = (2/π) arctan r`. -/
theorem gaussian_ratio_cauchy (m : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ m X) (j k : ℕ)
    (hj : j < m) (hk : k < m) (hjk : j ≠ k) (r : ℝ) (hr : 0 ≤ r) :
    μ.real {ω | |X j ω / X k ω| ≤ r} = 2 / π * arctan r := by
  set Y : ℕ → Ω → ℝ := fun i => if i = 0 then X j else X k with hYdef
  set g : Fin 2 → Fin m := fun i => if (i : ℕ) = 0 then ⟨j, hj⟩ else ⟨k, hk⟩ with hgdef
  have hg : Function.Injective g := by
    intro a b hab
    have hab' := congrArg Fin.val hab
    fin_cases a <;> fin_cases b <;> simp [g] at hab' ⊢ <;> omega
  have hYg : (fun i : Fin (1 + 1) => Y i) = fun i => X (g i) := by
    funext i; fin_cases i <;> simp [Y, g]
  have hY : IidStdGaussian μ (1 + 1) Y := by
    refine ⟨fun i hi => ?_, ?_⟩
    · by_cases h0 : i = 0
      · simp only [Y, h0, ZeroCert.zc_if_pos]; exact hX.gauss j hj
      · simp only [Y, h0, ZeroCert.zc_if_neg, not_false_eq_true]; exact hX.gauss k hk
    · rw [hYg]; exact hX.indep.precomp hg
  have h := ratio_law μ 1 Y hY r hr
  rw [ratioLaw_one hr] at h
  rw [← h]
  congr 1; ext ω; simp [Y]

/-- **Proposition 4.3 (Union-bound form).** `I_n(r) ≥ 1 - n (1 - (2/π) arctan r)`. -/
theorem ratio_union_bound (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (r : ℝ)
    (hr : 0 ≤ r) : 1 - n * (1 - 2 / π * arctan r) ≤ ratioLaw n r := by
  rw [← ratio_law μ n X hX r hr]
  have hmeas : ∀ k, k ≤ n → Measurable (fun ω => |X k ω / X n ω|) := fun k hk =>
    ((hX.measurable (by omega)).div (hX.measurable (by omega))).abs
  have hcov : {ω | ∀ k < n, |X k ω / X n ω| ≤ r}ᶜ ⊆ ⋃ k ∈ range n, {ω | r < |X k ω / X n ω|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, ZeroCert.zc_mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range, ZeroCert.zc_mem_setOf_eq]
    exact ⟨k, hk, hlt⟩
  have hU : MeasurableSet (⋃ k ∈ range n, {ω | r < |X k ω / X n ω|}) :=
    Finset.measurableSet_biUnion _ (fun k hk => measurableSet_lt measurable_const
      (hmeas k (by have := Finset.mem_range.mp hk; omega)))
  have h1 := one_sub_le_measureReal μ hU hcov
  have h2 : μ.real (⋃ k ∈ range n, {ω | r < |X k ω / X n ω|}) ≤ n * (1 - 2 / π * arctan r) := by
    calc μ.real (⋃ k ∈ range n, {ω | r < |X k ω / X n ω|})
        ≤ ∑ k ∈ range n, μ.real {ω | r < |X k ω / X n ω|} := measureReal_biUnion_finset_le _ _
      _ = ∑ k ∈ range n, (1 - 2 / π * arctan r) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk := Finset.mem_range.mp hk
          have hc := gaussian_ratio_cauchy μ (n + 1) X hX k n (by omega) (by omega) hk.ne r hr
          have hcompl : {ω | r < |X k ω / X n ω|} = {ω | |X k ω / X n ω| ≤ r}ᶜ := by
            ext ω; simp
          rw [hcompl, measureReal_compl (measurableSet_le (hmeas k hk.le) measurable_const), hc]
          simp
      _ = n * (1 - 2 / π * arctan r) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

lemma arctan_cot {x : ℝ} (hx0 : 0 < x) (hx1 : x < π / 2) : arctan (cot x) = π / 2 - x := by
  rw [cot_eq_cos_div_sin, ← inv_div, ← tan_eq_sin_div_cos, ← tan_pi_div_two_sub, arctan_tan]
    <;> linarith

/-- **Proposition 4.3, radius.** `ℙ{ρ_z(Q_n) ≤ 1 + cot(π δ/(2n))} ≥ 1 - δ`. -/
theorem ratio_union_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ containProb μ n (realCoeff X) (1 + cot (π * δ / (2 * n))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < π * δ / (2 * n) := by positivity
  have hx1 : π * δ / (2 * n) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos]
  have hcot : 0 ≤ cot (π * δ / (2 * n)) := by
    rw [cot_eq_cos_div_sin]
    exact div_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hx1.le⟩)
      (sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith [pi_pos]))
  have h1 := ratio_union_bound μ n X hX _ hcot
  have h2 := ratio_certificate μ hC n X hX (1 + cot (π * δ / (2 * n))) (by linarith)
  rw [add_sub_cancel_left] at h2
  rw [arctan_cot hx0 hx1] at h1
  have : 1 - (n : ℝ) * (1 - 2 / π * (π / 2 - π * δ / (2 * n))) = 1 - δ := by
    field_simp; ring
  linarith

/-- **Proposition 4.4 (Vieta upper bound for Gaussian polynomials).**
`Π_{Q_n}(c) ≤ (2/π) arctan(c^n)`. -/
theorem vieta_gauss_upper (hV : VietaBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (c : ℝ) (hc : 0 ≤ c) :
    containProb μ n (realCoeff X) c ≤ 2 / π * arctan (c ^ n) := by
  rw [← gaussian_ratio_cauchy μ (n + 1) X hX 0 n (by omega) (by omega) (by omega) _
    (by positivity)]
  apply measureReal_mono_ae'
  filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω hall
  have hωc : (X n ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hnorm : ZerosWithin n (fun k => realCoeff X k ω / realCoeff X n ω) c := by
    intro z hz
    apply hall z
    unfold peval at hz ⊢
    have : ∑ k ∈ range (n + 1), realCoeff X k ω / realCoeff X n ω * z ^ k =
        (∑ k ∈ range (n + 1), realCoeff X k ω * z ^ k) / realCoeff X n ω := by
      rw [Finset.sum_div]; congr 1; funext k; ring
    rw [this, div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hz
    · exact absurd hz hωc
  have := hV n _ c hn (by simp [realCoeff, hωc]) hc hnorm
  simpa [realCoeff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_div] using this

/-- **Remark 4.5, second identity.** `I_n(1) = 1/(n+1)`. -/
theorem ratioLaw_at_one (n : ℕ) : ratioLaw n 1 = 1 / (n + 1) := by
  rw [ratioLaw_eq_ratioJ n zero_le_one]
  unfold ratioJ
  simp only [one_mul]
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun x => hnCDF x ^ (n + 1) / (n + 1))
      (hnDens x * hnCDF x ^ n) x := by
    intro x hx
    have := ((hnCDF_hasDerivAt hx).pow (n + 1)).div_const ((n : ℝ) + 1)
    convert this using 1
    push_cast
    field_simp
  have hcont : ContinuousWithinAt (fun x => hnCDF x ^ (n + 1) / (n + 1)) (Set.Ici 0) 0 :=
    ((hnCDF_continuous.pow (n + 1)).div_const _).continuousWithinAt
  have hlim : Tendsto (fun x => hnCDF x ^ (n + 1) / (n + 1)) atTop (𝓝 (1 / (n + 1))) := by
    have := (hnCDF_tendsto_one.pow (n + 1)).div_const ((n : ℝ) + 1)
    simpa using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (ratioJ_integrableOn n 1 |>.congr_fun
    (fun x _ => by simp) measurableSet_Ioi) hlim]
  simp [hnCDF_zero]

end ZeroCert

end


-- =====================================================================
-- Part: DegreeFree
-- =====================================================================

section

/-!
# Section 6.1: conditioning, small-ball bounds and degree-independent radii
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-! ### Deterministic Rouché-type dominance (elementary) -/

/-- A zero `z ≠ 0` satisfies `|a_n| ≤ ∑_{k<n} |a_k| |z|^{k-n}`. -/
lemma norm_lead_le_cauchyG_of_zero (n : ℕ) (a : ℕ → ℂ) (z : ℂ) (hz0 : z ≠ 0)
    (hz : peval n a z = 0) : ‖a n‖ ≤ cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  unfold peval at hz
  rw [Finset.sum_range_succ] at hz
  have h1 : a n * z ^ n = -∑ k ∈ range n, a k * z ^ k := by linear_combination hz
  have h2 : ‖a n‖ * ‖z‖ ^ n ≤ ∑ k ∈ range n, ‖a k‖ * ‖z‖ ^ k := by
    rw [← norm_pow, ← norm_mul, h1, norm_neg]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have h3 : cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ = (∑ k ∈ range n, ‖a k‖ * ‖z‖ ^ k) / ‖z‖ ^ n := by
    unfold cauchyG
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    rw [inv_pow, mul_div_assoc]
    congr 1
    rw [show n = (n - k) + k from (Nat.sub_add_cancel hk.le).symm, pow_add]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  exact h2

/-- **Weighted Rouché dominance.** If `S_R = ∑_{j=1}^n |a_{n-j}| R^{-j} < |a_n|`, then every
zero of `P` lies in `|z| < R`. -/
lemma zeros_lt_of_dominance (n : ℕ) (a : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hdom : cauchyF n (fun k => ‖a k‖) R < ‖a n‖) (z : ℂ) (hz : peval n a z = 0) : ‖z‖ < R := by
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero]; exact hR
  have h := norm_lead_le_cauchyG_of_zero n a z hz0 hz
  by_contra hle
  push Not at hle
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have : cauchyG n (fun k => ‖a k‖) ‖z‖⁻¹ ≤ cauchyG n (fun k => ‖a k‖) R⁻¹ :=
    cauchyG_mono n _ (fun k _ => norm_nonneg _) (inv_nonneg.mpr hzn.le)
      (inv_anti₀ hR hle)
  rw [cauchyF_eq] at hdom
  linarith

/-! ### Elementary sums -/

lemma sum_range_pow_sub (n : ℕ) (q : ℝ) (hq : q ≠ 1) :
    ∑ k ∈ range n, q ^ (n - k) = q * (1 - q ^ n) / (1 - q) := by
  have h1 : ∑ k ∈ range n, q ^ (n - k) = ∑ j ∈ range n, q ^ (j + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    congr 1; omega
  rw [h1]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq hq]
  have : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  field_simp
  ring

/-- `∑_{j=1}^n R^{-j} = (1 - R^{-n})/(R - 1)`. -/
lemma sum_range_inv_pow (n : ℕ) {R : ℝ} (hR : 1 < R) :
    ∑ k ∈ range n, (R⁻¹) ^ (n - k) = (1 - (R⁻¹) ^ n) / (R - 1) := by
  have hq : R⁻¹ ≠ 1 := by
    intro h; have := inv_eq_one.mp h; linarith
  rw [sum_range_pow_sub n R⁻¹ hq]
  have h1 : R - 1 ≠ 0 := by linarith
  have h2 : R ≠ 0 := by linarith
  have h3 : 1 - R⁻¹ ≠ 0 := by
    intro h; apply hq; linarith
  field_simp

lemma sum_range_inv_pow_le (n : ℕ) {R : ℝ} (hR : 1 < R) :
    ∑ k ∈ range n, (R⁻¹) ^ (n - k) ≤ 1 / (R - 1) := by
  rw [sum_range_inv_pow n hR]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : 0 ≤ (R⁻¹) ^ n := by positivity
  linarith

/-- Subadditivity of `x ↦ x^β` for `0 < β ≤ 1` over finite sums. -/
lemma rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) : (∑ i ∈ s, x i) ^ β ≤ ∑ i ∈ s, x i ^ β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hβ0.ne']
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hxi : 0 ≤ x i := hx i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, 0 ≤ x j := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have h1 := Real.rpow_add_le_add_rpow hxi (Finset.sum_nonneg hs) hβ0.le hβ1
    linarith [ih hs]

/-! ### The small-ball transfer theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The weighted sum `S_R = ∑_{j=1}^n |A_{n-j}| R^{-j}` of a random polynomial. -/
noncomputable def weightedSum (n : ℕ) (A : ℕ → Ω → ℂ) (R : ℝ) (ω : Ω) : ℝ :=
  cauchyF n (fun k => ‖A k ω‖) R

omit [MeasurableSpace Ω] in
lemma weightedSum_eq (n : ℕ) (A : ℕ → Ω → ℂ) (R : ℝ) (ω : Ω) :
    weightedSum n A R ω = ∑ k ∈ range n, (R⁻¹) ^ (n - k) * ‖A k ω‖ := by
  unfold weightedSum cauchyF
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

omit [MeasurableSpace Ω] in
lemma weightedSum_nonneg (n : ℕ) (A : ℕ → Ω → ℂ) {R : ℝ} (hR : 0 < R) (ω : Ω) :
    0 ≤ weightedSum n A R ω := by
  rw [weightedSum_eq]
  exact Finset.sum_nonneg (fun k _ => by positivity)

lemma measurable_weightedSum (n : ℕ) (A : ℕ → Ω → ℂ) (hA : ∀ k < n, Measurable (A k)) (R : ℝ) :
    Measurable (weightedSum n A R) := by
  have : weightedSum n A R = fun ω => ∑ k ∈ range n, (R⁻¹) ^ (n - k) * ‖A k ω‖ :=
    funext (weightedSum_eq n A R)
  rw [this]
  exact Finset.measurable_sum _ (fun k hk => measurable_const.mul
    (hA k (Finset.mem_range.mp hk)).norm)

/-- Failure of the zero bound implies failure of the weighted dominance condition. -/
lemma rootTail_le_prob_dominance_fails (n : ℕ) (A : ℕ → Ω → ℂ) {R : ℝ} (hR : 0 < R) :
    rootTail μ n A R ≤ μ.real {ω | ‖A n ω‖ ≤ weightedSum n A R ω} := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨z, hz, hRz⟩
  by_contra hcon
  simp only [ZeroCert.zc_mem_setOf_eq, not_le] at hcon
  have := zeros_lt_of_dominance n (fun k => A k ω) hR hcon z hz
  linarith

/-- Conditioning on the lower coefficients: `ℙ{T ≤ S_R} ≤ C₀ 𝔼[S_R^β]`. -/
lemma prob_dominance_fails_le (n : ℕ) (A : ℕ → Ω → ℂ) (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (β C0 : ℝ) (hsmall : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} ≤ C0 * t ^ β)
    {R : ℝ} (hR : 0 < R) (hint : Integrable (fun ω => weightedSum n A R ω ^ β) μ) :
    μ.real {ω | ‖A n ω‖ ≤ weightedSum n A R ω} ≤ C0 * ∫ ω, weightedSum n A R ω ^ β ∂μ := by
  set V : Ω → (Fin n → ℂ) := fun ω k => A k ω
  set φ : (Fin n → ℂ) → ℝ := fun v => ∑ k : Fin n, (R⁻¹) ^ (n - (k : ℕ)) * ‖v k‖
  have hφ : Measurable φ := Finset.measurable_sum _ (fun k _ => measurable_const.mul
    (measurable_pi_apply k).norm)
  have hVm : Measurable V := zc_measurable_pi (fun k => hA k (by omega))
  have hSφ : ∀ ω, weightedSum n A R ω = φ (V ω) := by
    intro ω; rw [weightedSum_eq, Finset.sum_range]
  set S : Set (ℝ × (Fin n → ℂ)) := {p | p.1 ≤ φ p.2}
  have hS : MeasurableSet S := measurableSet_le measurable_fst (hφ.comp measurable_snd)
  have hset : {ω | ‖A n ω‖ ≤ weightedSum n A R ω} = {ω | (‖A n ω‖, V ω) ∈ S} := by
    ext ω; simp only [ZeroCert.zc_mem_setOf_eq, S, hSφ]
  rw [hset, indep_measureReal_eq_integral μ _ V (hA n le_rfl).norm hVm hind S hS,
    ← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ (fun ω => measureReal_nonneg)) (hint.const_mul C0)
  refine ae_of_all _ (fun ω => ?_)
  have := hsmall (weightedSum n A R ω) (weightedSum_nonneg n A hR ω)
  simp only [S, ZeroCert.zc_mem_setOf_eq, ← hSφ]
  exact this

/-- **Theorem 6.1 (Small-ball transfer), case `0 < β ≤ 1`.** -/
theorem smallBall_tail_le_one (n : ℕ) (A : ℕ → Ω → ℂ) (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (β C0 m : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hC0 : 0 ≤ C0)
    (hsmall : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} ≤ C0 * t ^ β)
    (hmint : ∀ k < n, Integrable (fun ω => ‖A k ω‖ ^ β) μ)
    (hmom : ∀ k < n, ∫ ω, ‖A k ω‖ ^ β ∂μ ≤ m) (R : ℝ) (hR : 1 < R) :
    rootTail μ n A R ≤ C0 * m * (1 - R ^ (-((n : ℝ) * β))) / (R ^ β - 1) := by
  have hR0 : 0 < R := by linarith
  set w : ℕ → ℝ := fun k => (R⁻¹) ^ (n - k)
  have hw : ∀ k, 0 ≤ w k := fun k => by positivity
  -- pointwise subadditivity
  have hpt : ∀ ω, weightedSum n A R ω ^ β ≤ ∑ k ∈ range n, w k ^ β * ‖A k ω‖ ^ β := by
    intro ω
    rw [weightedSum_eq]
    refine (rpow_sum_le_sum_rpow _ _ (fun k _ => by positivity) hβ0 hβ1).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun k _ => Real.mul_rpow (hw k) (norm_nonneg _))
  have hbint : Integrable (fun ω => ∑ k ∈ range n, w k ^ β * ‖A k ω‖ ^ β) μ :=
    zc_integrable_finset_sum _ (fun k hk => (hmint k (Finset.mem_range.mp hk)).const_mul _)
  have hint : Integrable (fun ω => weightedSum n A R ω ^ β) μ := by
    refine hbint.mono' ?_ (ae_of_all _ (fun ω => ?_))
    · exact ((measurable_weightedSum n A (fun k hk => hA k hk.le) R).pow_const β).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (weightedSum_nonneg n A hR0 ω) _)]
      exact hpt ω
  have hE : ∫ ω, weightedSum n A R ω ^ β ∂μ ≤ m * ∑ k ∈ range n, w k ^ β := by
    calc ∫ ω, weightedSum n A R ω ^ β ∂μ
        ≤ ∫ ω, ∑ k ∈ range n, w k ^ β * ‖A k ω‖ ^ β ∂μ :=
          integral_mono hint hbint (fun ω => hpt ω)
      _ = ∑ k ∈ range n, w k ^ β * ∫ ω, ‖A k ω‖ ^ β ∂μ := by
          rw [zc_integral_finset_sum _ (fun k hk => (hmint k (Finset.mem_range.mp hk)).const_mul _)]
          exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
      _ ≤ ∑ k ∈ range n, w k ^ β * m := Finset.sum_le_sum (fun k hk =>
          mul_le_mul_of_nonneg_left (hmom k (Finset.mem_range.mp hk))
            (Real.rpow_nonneg (hw k) _))
      _ = m * ∑ k ∈ range n, w k ^ β := by rw [Finset.mul_sum]; simp_rw [mul_comm]
  have hgeom : ∑ k ∈ range n, w k ^ β = (1 - R ^ (-((n : ℝ) * β))) / (R ^ β - 1) := by
    have hq : ∀ k, w k ^ β = ((R ^ β)⁻¹) ^ (n - k) := by
      intro k
      simp only [w]
      rw [← Real.rpow_pow_comm (inv_nonneg.mpr hR0.le), Real.inv_rpow hR0.le]
    simp_rw [hq]
    have hRb : 1 < R ^ β := Real.one_lt_rpow hR hβ0
    rw [sum_range_inv_pow n hRb]
    congr 2
    rw [show -((n : ℝ) * β) = -(β * n) by ring, Real.rpow_neg hR0.le, Real.rpow_mul hR0.le,
      Real.rpow_natCast, inv_pow]
  have h1 := rootTail_le_prob_dominance_fails μ n A hR0
  have h2 := prob_dominance_fails_le μ n A hA hind β C0 hsmall hR0 hint
  rw [hgeom] at hE
  calc rootTail μ n A R ≤ C0 * ∫ ω, weightedSum n A R ω ^ β ∂μ := h1.trans h2
    _ ≤ C0 * (m * ((1 - R ^ (-((n : ℝ) * β))) / (R ^ β - 1))) :=
        mul_le_mul_of_nonneg_left hE hC0
    _ = C0 * m * (1 - R ^ (-((n : ℝ) * β))) / (R ^ β - 1) := by ring

/-- **Theorem 6.1 (Small-ball transfer), case `β ≥ 1`.** -/
theorem smallBall_tail_ge_one (n : ℕ) (hn : 1 ≤ n) (A : ℕ → Ω → ℂ)
    (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (β C0 m : ℝ) (hβ1 : 1 ≤ β) (hC0 : 0 ≤ C0)
    (hsmall : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} ≤ C0 * t ^ β)
    (hmint : ∀ k < n, Integrable (fun ω => ‖A k ω‖ ^ β) μ)
    (hmom : ∀ k < n, ∫ ω, ‖A k ω‖ ^ β ∂μ ≤ m) (R : ℝ) (hR : 1 < R) :
    rootTail μ n A R ≤ C0 * m * ((1 - (R⁻¹) ^ n) / (R - 1)) ^ β := by
  have hR0 : 0 < R := by linarith
  set w : ℕ → ℝ := fun k => (R⁻¹) ^ (n - k)
  have hw : ∀ k, 0 ≤ w k := fun k => by positivity
  set W := ∑ k ∈ range n, w k
  have hWpos : 0 < W := by
    apply Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.mpr (by omega)⟩
  -- pointwise Jensen
  have hpt : ∀ ω, weightedSum n A R ω ^ β ≤ W ^ (β - 1) * ∑ k ∈ range n, w k * ‖A k ω‖ ^ β := by
    intro ω
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow (s := range n) (fun k => w k / W)
      (fun k => ‖A k ω‖) (fun k _ => by positivity)
      (by rw [← Finset.sum_div, div_self hWpos.ne']) (fun k _ => norm_nonneg _) hβ1
    have hS : weightedSum n A R ω = W * ∑ k ∈ range n, w k / W * ‖A k ω‖ := by
      rw [weightedSum_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [show W * (w k / W * ‖A k ω‖) = w k * ‖A k ω‖ by field_simp])
    rw [hS, Real.mul_rpow hWpos.le (Finset.sum_nonneg (fun k _ => by positivity))]
    calc W ^ β * (∑ k ∈ range n, w k / W * ‖A k ω‖) ^ β
        ≤ W ^ β * ∑ k ∈ range n, w k / W * ‖A k ω‖ ^ β :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = W ^ (β - 1) * ∑ k ∈ range n, w k * ‖A k ω‖ ^ β := by
          rw [Real.rpow_sub hWpos, Real.rpow_one, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by field_simp)
  have hbint : Integrable (fun ω => W ^ (β - 1) * ∑ k ∈ range n, w k * ‖A k ω‖ ^ β) μ :=
    (zc_integrable_finset_sum _ (fun k hk => (hmint k (Finset.mem_range.mp hk)).const_mul _)).const_mul _
  have hint : Integrable (fun ω => weightedSum n A R ω ^ β) μ := by
    refine hbint.mono' ?_ (ae_of_all _ (fun ω => ?_))
    · exact ((measurable_weightedSum n A (fun k hk => hA k hk.le) R).pow_const β).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (weightedSum_nonneg n A hR0 ω) _)]
      exact hpt ω
  have hE : ∫ ω, weightedSum n A R ω ^ β ∂μ ≤ m * W ^ β := by
    calc ∫ ω, weightedSum n A R ω ^ β ∂μ
        ≤ ∫ ω, W ^ (β - 1) * ∑ k ∈ range n, w k * ‖A k ω‖ ^ β ∂μ :=
          integral_mono hint hbint (fun ω => hpt ω)
      _ = W ^ (β - 1) * ∑ k ∈ range n, w k * ∫ ω, ‖A k ω‖ ^ β ∂μ := by
          rw [integral_const_mul, zc_integral_finset_sum _ (fun k hk =>
            (hmint k (Finset.mem_range.mp hk)).const_mul _)]
          congr 1
          exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
      _ ≤ W ^ (β - 1) * ∑ k ∈ range n, w k * m :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk =>
            mul_le_mul_of_nonneg_left (hmom k (Finset.mem_range.mp hk)) (hw k))) (by positivity)
      _ = m * W ^ β := by
          rw [← Finset.sum_mul]
          change W ^ (β - 1) * (W * m) = m * W ^ β
          rw [Real.rpow_sub hWpos, Real.rpow_one]
          field_simp
  have h1 := rootTail_le_prob_dominance_fails μ n A hR0
  have h2 := prob_dominance_fails_le μ n A hA hind β C0 hsmall hR0 hint
  have hW : W = (1 - (R⁻¹) ^ n) / (R - 1) := sum_range_inv_pow n hR
  calc rootTail μ n A R ≤ C0 * ∫ ω, weightedSum n A R ω ^ β ∂μ := h1.trans h2
    _ ≤ C0 * (m * W ^ β) := mul_le_mul_of_nonneg_left hE hC0
    _ = C0 * m * ((1 - (R⁻¹) ^ n) / (R - 1)) ^ β := by rw [hW]; ring

/-- If `ℙ{ρ_z > R} = 0` for every `R > 1`, then also `ℙ{ρ_z > 1} = 0`. -/
lemma rootTail_one_eq_zero (n : ℕ) (A : ℕ → Ω → ℂ) (h : ∀ R, 1 < R → rootTail μ n A R ≤ 0) :
    rootTail μ n A 1 = 0 := by
  have hU : {ω | ∃ z, peval n (fun k => A k ω) z = 0 ∧ 1 < ‖z‖} =
      ⋃ j : ℕ, {ω | ∃ z, peval n (fun k => A k ω) z = 0 ∧ 1 + 1 / ((j : ℝ) + 1) < ‖z‖} := by
    ext ω; simp only [ZeroCert.zc_mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, h1⟩
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr h1)
      exact ⟨j, z, hz, by linarith⟩
    · rintro ⟨j, z, hz, h1⟩
      exact ⟨z, hz, by have : 0 < 1 / ((j : ℝ) + 1) := by positivity
                       linarith⟩
  have hnull : ∀ j : ℕ, μ {ω | ∃ z, peval n (fun k => A k ω) z = 0 ∧
      1 + 1 / ((j : ℝ) + 1) < ‖z‖} = 0 := by
    intro j
    have hj := h (1 + 1 / ((j : ℝ) + 1)) (by have : 0 < 1 / ((j : ℝ) + 1) := by positivity
                                             linarith)
    have h0 : rootTail μ n A (1 + 1 / ((j : ℝ) + 1)) = 0 := le_antisymm hj measureReal_nonneg
    unfold rootTail at h0
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0
  unfold rootTail
  rw [hU, measureReal_def, measure_iUnion_null hnull]
  simp

/-- **Theorem 6.1, degree-independent radius, case `0 < β ≤ 1`:**
`R_δ = (1 + C₀ m_β/δ)^{1/β}` is a probabilistic zero bound at confidence `1 - δ`. -/
theorem smallBall_radius_le_one (n : ℕ) (A : ℕ → Ω → ℂ) (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (β C0 m : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hC0 : 0 ≤ C0) (hm : 0 ≤ m)
    (hsmall : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} ≤ C0 * t ^ β)
    (hmint : ∀ k < n, Integrable (fun ω => ‖A k ω‖ ^ β) μ)
    (hmom : ∀ k < n, ∫ ω, ‖A k ω‖ ^ β ∂μ ≤ m) (δ : ℝ) (hδ0 : 0 < δ) :
    1 - δ ≤ containProb μ n A ((1 + C0 * m / δ) ^ (1 / β)) := by
  have hsum := containProb_add_rootTail μ n A hA ((1 + C0 * m / δ) ^ (1 / β))
  have htail : ∀ R, 1 < R → rootTail μ n A R ≤ C0 * m / (R ^ β - 1) := by
    intro R hR
    have h := smallBall_tail_le_one μ n A hA hind β C0 m hβ0 hβ1 hC0 hsmall hmint hmom R hR
    have hRb : 0 < R ^ β - 1 := by have := Real.one_lt_rpow hR hβ0; linarith
    refine h.trans ?_
    rw [div_le_div_iff_of_pos_right hRb]
    have : 0 ≤ R ^ (-((n : ℝ) * β)) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ C0 * m := mul_nonneg hC0 hm
    nlinarith
  rcases (mul_nonneg hC0 hm).lt_or_eq with hpos | hzero
  · set R := (1 + C0 * m / δ) ^ (1 / β)
    have hRβ : R ^ β = 1 + C0 * m / δ := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ0.ne', Real.rpow_one]
    have hR : 1 < R := by
      apply Real.one_lt_rpow (by have : 0 < C0 * m / δ := by positivity
                                 linarith) (by positivity)
    have h := htail R hR
    have hne : C0 * m ≠ 0 := hpos.ne'
    have hδ : C0 * m / (C0 * m / δ) = δ := by
      rw [div_div_eq_mul_div, mul_div_right_comm, div_self hne, one_mul]
    rw [hRβ, add_sub_cancel_left, hδ] at h
    linarith
  · have hR1 : (1 + C0 * m / δ) ^ (1 / β) = 1 := by rw [← hzero]; simp
    rw [hR1] at hsum ⊢
    have := rootTail_one_eq_zero μ n A (fun R hR => by
      have := htail R hR; rwa [← hzero, zero_div] at this)
    linarith

/-- **Theorem 6.1, degree-independent radius, case `β ≥ 1`:**
`R_δ = 1 + (C₀ m_β/δ)^{1/β}` is a probabilistic zero bound at confidence `1 - δ`. -/
theorem smallBall_radius_ge_one (n : ℕ) (hn : 1 ≤ n) (A : ℕ → Ω → ℂ)
    (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (β C0 m : ℝ) (hβ1 : 1 ≤ β) (hC0 : 0 ≤ C0) (hm : 0 ≤ m)
    (hsmall : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} ≤ C0 * t ^ β)
    (hmint : ∀ k < n, Integrable (fun ω => ‖A k ω‖ ^ β) μ)
    (hmom : ∀ k < n, ∫ ω, ‖A k ω‖ ^ β ∂μ ≤ m) (δ : ℝ) (hδ0 : 0 < δ) :
    1 - δ ≤ containProb μ n A (1 + (C0 * m / δ) ^ (1 / β)) := by
  have hβ0 : 0 < β := by linarith
  have hsum := containProb_add_rootTail μ n A hA (1 + (C0 * m / δ) ^ (1 / β))
  have htail : ∀ R, 1 < R → rootTail μ n A R ≤ C0 * m * (1 / (R - 1)) ^ β := by
    intro R hR
    have h := smallBall_tail_ge_one μ n hn A hA hind β C0 m hβ1 hC0 hsmall hmint hmom R hR
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hm))
    apply Real.rpow_le_rpow (div_nonneg (by
      have : (R⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR.le)
      linarith) (by linarith)) _ hβ0.le
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 ≤ (R⁻¹) ^ n := by positivity
    linarith
  rcases (mul_nonneg hC0 hm).lt_or_eq with hpos | hzero
  · set t := (C0 * m / δ) ^ (1 / β)
    have ht : 0 < t := by positivity
    have htβ : t ^ β = C0 * m / δ := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ0.ne', Real.rpow_one]
    have h := htail (1 + t) (by linarith)
    rw [add_sub_cancel_left, Real.div_rpow zero_le_one ht.le, Real.one_rpow, htβ,
      one_div_div, mul_div_assoc', mul_comm (C0 * m) δ, mul_div_assoc, div_self hpos.ne',
      mul_one] at h
    linarith
  · have hR1 : (1 + (C0 * m / δ) ^ (1 / β)) = 1 := by
      rw [← hzero, zero_div, Real.zero_rpow (by positivity), add_zero]
    rw [hR1] at hsum ⊢
    have := rootTail_one_eq_zero μ n A (fun R hR => by
      have := htail R hR; rwa [← hzero, zero_mul] at this)
    linarith

end ZeroCert

end


-- =====================================================================
-- Part: GaussDegreeFree
-- =====================================================================

section

/-!
# Section 6.1 (continued): the real Gaussian confidence radius and other coefficient laws
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma IidStdGaussian.measurable_realCoeff {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ (n + 1) X) :
    ∀ k ≤ n, Measurable (realCoeff X k) := fun k hk =>
  Complex.measurable_ofReal.comp (hX.measurable (by omega))

lemma IidStdGaussian.indep_lead_realCoeff {n : ℕ} {X : ℕ → Ω → ℝ}
    (hX : IidStdGaussian μ (n + 1) X) :
    IndepFun (fun ω => ‖realCoeff X n ω‖) (fun ω (k : Fin n) => realCoeff X k ω) μ := by
  have h := hX.indep_init_last.comp (φ := fun (v : Fin n → ℝ) (k : Fin n) => (v k : ℂ))
    (ψ := fun x : ℝ => |x|)
    (zc_measurable_pi (fun k => Complex.measurable_ofReal.comp (measurable_pi_apply k)))
    measurable_abs
  have e1 : (fun ω => ‖realCoeff X n ω‖) = (fun x : ℝ => |x|) ∘ X n := by
    funext ω; simp [realCoeff]
  have e2 : (fun ω (k : Fin n) => realCoeff X k ω) =
      (fun (v : Fin n → ℝ) (k : Fin n) => (v k : ℂ)) ∘ (fun ω (k : Fin n) => X k ω) := rfl
  rw [e1, e2]; exact h.symm

variable (μ) [IsProbabilityMeasure μ]

/-- **Corollary 6.2 (Real Gaussian confidence radius), tail bound.**
`ℙ{ρ_z(Q_n) > R} ≤ (2/π)(1 - R^{-n})/(R - 1) ≤ 2/(π(R-1))` for every `R > 1`. -/
theorem gaussian_degree_free_tail (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    (R : ℝ) (hR : 1 < R) :
    rootTail μ n (realCoeff X) R ≤ 2 / π * (1 - (R⁻¹) ^ n) / (R - 1) ∧
    2 / π * (1 - (R⁻¹) ^ n) / (R - 1) ≤ 2 / (π * (R - 1)) := by
  have hR0 : 0 < R := by linarith
  have h := smallBall_tail_le_one μ n (realCoeff X) hX.measurable_realCoeff
    hX.indep_lead_realCoeff 1 h0 h0 one_pos le_rfl h0_pos.le
    (fun t ht => by
      rw [Real.rpow_one]
      have := (hX.gauss n (by omega)).prob_norm_le μ t
      simp only [realCoeff] at this ⊢
      rw [this]; exact hnCDF_le_mul t ht)
    (fun k hk => by
      simp only [Real.rpow_one, realCoeff, Complex.norm_real, Real.norm_eq_abs]
      exact (hX.gauss k (by omega)).integrable_abs μ)
    (fun k hk => by
      simp only [Real.rpow_one, realCoeff, Complex.norm_real, Real.norm_eq_abs]
      rw [(hX.gauss k (by omega)).integral_abs μ]) R hR
  have hconv : h0 * h0 * (1 - R ^ (-((n : ℝ) * 1))) / (R ^ (1 : ℝ) - 1) =
      2 / π * (1 - (R⁻¹) ^ n) / (R - 1) := by
    rw [← sq, h0_sq, mul_one, Real.rpow_one, Real.rpow_neg hR0.le, Real.rpow_natCast, inv_pow]
  refine ⟨h.trans (le_of_eq hconv), ?_⟩
  have hR1 : 0 < R - 1 := by linarith
  rw [show 2 / (π * (R - 1)) = 2 / π * 1 / (R - 1) by field_simp]
  apply div_le_div_of_nonneg_right _ hR1.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : 0 ≤ (R⁻¹) ^ n := by positivity
  linarith

/-- **Corollary 6.2, radius.** For every `n` and `0 < δ < 1`,
`ℙ{ρ_z(Q_n) ≤ 1 + 2/(π δ)} ≥ 1 - δ`. -/
theorem gaussian_degree_free_radius (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    (δ : ℝ) (hδ0 : 0 < δ) :
    1 - δ ≤ containProb μ n (realCoeff X) (1 + 2 / (π * δ)) := by
  have h := smallBall_radius_le_one μ n (realCoeff X) hX.measurable_realCoeff
    hX.indep_lead_realCoeff 1 h0 h0 one_pos le_rfl h0_pos.le h0_pos.le
    (fun t ht => by
      rw [Real.rpow_one]
      have := (hX.gauss n (by omega)).prob_norm_le μ t
      simp only [realCoeff] at this ⊢
      rw [this]; exact hnCDF_le_mul t ht)
    (fun k hk => by
      simp only [Real.rpow_one, realCoeff, Complex.norm_real, Real.norm_eq_abs]
      exact (hX.gauss k (by omega)).integrable_abs μ)
    (fun k hk => by
      simp only [Real.rpow_one, realCoeff, Complex.norm_real, Real.norm_eq_abs]
      rw [(hX.gauss k (by omega)).integral_abs μ]) δ hδ0
  rwa [div_one, Real.rpow_one, ← sq, h0_sq, div_div] at h

/-- **Remark 6.3 (circular complex Gaussian coefficients).** If `ℙ{|A_n| ≤ t} = 1 - e^{-t²}`,
`𝔼|A_k|² = 1`, and `A_n` is independent of the other coefficients, then `1 + δ^{-1/2}` is a
degree-independent confidence radius at level `1 - δ`. -/
theorem complex_gaussian_radius (n : ℕ) (hn : 1 ≤ n) (A : ℕ → Ω → ℂ)
    (hA : ∀ k ≤ n, Measurable (A k))
    (hind : IndepFun (fun ω => ‖A n ω‖) (fun ω (k : Fin n) => A k ω) μ)
    (hlaw : ∀ t, 0 ≤ t → μ.real {ω | ‖A n ω‖ ≤ t} = 1 - exp (-t ^ 2))
    (hmint : ∀ k < n, Integrable (fun ω => ‖A k ω‖ ^ (2 : ℝ)) μ)
    (hmom : ∀ k < n, ∫ ω, ‖A k ω‖ ^ (2 : ℝ) ∂μ = 1) (δ : ℝ) (hδ0 : 0 < δ) :
    1 - δ ≤ containProb μ n A (1 + (1 / δ) ^ (1 / (2 : ℝ))) := by
  have h := smallBall_radius_ge_one μ n hn A hA hind 2 1 1 (by norm_num) zero_le_one zero_le_one
    (fun t ht => by
      rw [hlaw t ht, one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have := Real.add_one_le_exp (-t ^ 2)
      linarith)
    hmint (fun k hk => (hmom k hk).le) δ hδ0
  simpa using h

/-- **Remark 6.3 (monic polynomials, Markov bound).** If `sup_k 𝔼|X_k| ≤ μ₀`, then
`ℙ{ρ_z(P_n) > R} ≤ μ₀/(R-1)` for `R > 1`, with no independence assumption at all. -/
theorem monic_markov_tail (n : ℕ) (X : ℕ → Ω → ℂ) (hXm : ∀ k < n, Measurable (X k))
    (μ0 : ℝ) (hμ0 : 0 ≤ μ0) (hint : ∀ k < n, Integrable (fun ω => ‖X k ω‖) μ)
    (hmom : ∀ k < n, ∫ ω, ‖X k ω‖ ∂μ ≤ μ0) (R : ℝ) (hR : 1 < R) :
    rootTail μ n (monicCoeff n X) R ≤ μ0 / (R - 1) := by
  have hA : ∀ k ≤ n, Measurable (monicCoeff n X k) := by
    intro k hk
    rcases hk.lt_or_eq with hk | hk
    · have : monicCoeff n X k = X k := funext (fun ω => monicCoeff_of_lt n X ω hk)
      rw [this]; exact hXm k hk
    · subst hk
      have : monicCoeff k X k = fun _ => 1 := funext (fun ω => monicCoeff_self k X ω)
      rw [this]; exact measurable_const
  have hlead : (fun ω => ‖monicCoeff n X n ω‖) = fun _ => (1 : ℝ) := by
    funext ω; rw [monicCoeff_self]; simp
  have hind : IndepFun (fun ω => ‖monicCoeff n X n ω‖) (fun ω (k : Fin n) => monicCoeff n X k ω) μ := by
    rw [hlead]; exact indepFun_const_left _ _
  have hlow : ∀ k < n, (fun ω => ‖monicCoeff n X k ω‖ ^ (1 : ℝ)) = fun ω => ‖X k ω‖ := by
    intro k hk; funext ω; rw [monicCoeff_of_lt n X ω hk, Real.rpow_one]
  have h := smallBall_tail_le_one μ n (monicCoeff n X) hA hind 1 1 μ0 one_pos le_rfl zero_le_one
    (fun t ht => by
      simp only [monicCoeff_self, norm_one, Real.rpow_one, one_mul]
      by_cases h1 : 1 ≤ t
      · exact measureReal_le_one.trans h1
      · have : {ω : Ω | (1 : ℝ) ≤ t} = ∅ := by ext; simp [h1]
        simp only [this, measureReal_empty]; exact ht)
    (fun k hk => by rw [hlow k hk]; exact hint k hk)
    (fun k hk => by rw [hlow k hk]; exact hmom k hk) R hR
  refine h.trans ?_
  rw [one_mul, Real.rpow_one]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : 0 ≤ R ^ (-((n : ℝ) * 1)) := Real.rpow_nonneg (by linarith) _
  nlinarith

end ZeroCert

end


-- =====================================================================
-- Part: Tail
-- =====================================================================

section

/-!
# Section 6.2: a uniform approximation to the extreme-root tail
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-! ### Elementary inequalities -/

lemma arctan_le_self' {u : ℝ} (hu : 0 ≤ u) : arctan u ≤ u := by
  have hmono : Monotone (fun x => x - arctan x) := by
    apply monotone_of_deriv_nonneg
    · exact differentiable_id.sub differentiable_arctan
    · intro x
      have hd : HasDerivAt (fun x => x - arctan x) (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id' x).sub (hasDerivAt_arctan x)
      rw [hd.deriv]
      have h1 : 1 / (1 + x ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]
      linarith
  have := hmono hu
  simp at this; linarith

lemma self_sub_cube_le_arctan {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 3 ≤ arctan u := by
  have hmono : Monotone (fun x => arctan x - x + x ^ 3 / 3) := by
    apply monotone_of_deriv_nonneg
    · exact ((differentiable_arctan.sub differentiable_id).add
        ((differentiable_id.pow 3).div_const 3))
    · intro x
      have hd : HasDerivAt (fun x => arctan x - x + x ^ 3 / 3)
          (1 / (1 + x ^ 2) - 1 + 3 * x ^ 2 / 3) x := by
        have := ((hasDerivAt_arctan x).sub (hasDerivAt_id x)).add
          ((hasDerivAt_pow 3 x).div_const 3)
        refine this.congr_deriv ?_
        norm_num
      rw [hd.deriv]
      have : 1 / (1 + x ^ 2) - 1 + 3 * x ^ 2 / 3 = x ^ 4 / (1 + x ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have := hmono hu
  simp at this; linarith

/-! ### Definitions -/

/-- `J(R) = (2/π) arctan(R⁻¹)`. -/
noncomputable def tailJ (R : ℝ) : ℝ := 2 / π * arctan R⁻¹

/-- `D_n(R) = (2/π) ∑_{j=2}^n R^{-j}`. -/
noncomputable def tailD (n : ℕ) (R : ℝ) : ℝ := 2 / π * ∑ j ∈ Ico 2 (n + 1), (R⁻¹) ^ j

/-- **Equation (6.6).** `D_n(R) = (2/π)(1 - R^{-(n-1)})/(R(R-1))`. -/
theorem tailD_eq (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) :
    tailD n R = 2 / π * (1 - (R⁻¹) ^ (n - 1)) / (R * (R - 1)) := by
  unfold tailD
  have hq : R⁻¹ ≠ 1 := by intro h; have := inv_eq_one.mp h; linarith
  have hs : ∑ j ∈ Ico 2 (n + 1), (R⁻¹) ^ j = (R⁻¹) ^ 2 * ∑ i ∈ range (n - 1), (R⁻¹) ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show n + 1 - 2 = n - 1 by omega]
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_add])
  rw [hs, geom_sum_eq hq]
  have h1 : R - 1 ≠ 0 := by linarith
  have h2 : R ≠ 0 := by linarith
  have h3 : R⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hq
  have hqR : R⁻¹ * R = 1 := inv_mul_cancel₀ h2
  rw [mul_div_assoc]
  congr 1
  rw [← mul_div_assoc, div_eq_div_iff h3 (mul_ne_zero h2 h1)]
  generalize (R⁻¹) ^ (n - 1) = t
  generalize R⁻¹ = q at hqR
  linear_combination (t - 1) * (q * R + 1 - q) * hqR

lemma tailD_nonneg (n : ℕ) {R : ℝ} (hR : 0 < R) : 0 ≤ tailD n R := by
  unfold tailD; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => by positivity))

lemma R_mul_tailD_le (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) :
    R * tailD n R ≤ 2 / (π * (R - 1)) := by
  rw [tailD_eq n hn hR]
  have hR0 : 0 < R := by linarith
  have hR1 : 0 < R - 1 := by linarith
  have : 0 ≤ (R⁻¹) ^ (n - 1) := by positivity
  rw [show R * (2 / π * (1 - R⁻¹ ^ (n - 1)) / (R * (R - 1))) =
    2 / π * (1 - R⁻¹ ^ (n - 1)) / (R - 1) by field_simp]
  rw [show 2 / (π * (R - 1)) = 2 / π * 1 / (R - 1) by field_simp]
  apply div_le_div_of_nonneg_right _ hR1.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- `B̂_R(Q_n)`: the implicit Cauchy radius of the normalized polynomial `Q_n / X_n`. -/
noncomputable def normImplicitCauchy {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  implicitCauchy n (fun k => |X k ω| / |X n ω|)

/-- `c_n(R) = ℙ{B̂_R(Q_n) > R}`, the failure probability of the implicit Cauchy certificate. -/
noncomputable def certTail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℝ) (R : ℝ) : ℝ :=
  μ.real {ω | R < normImplicitCauchy n X ω}

/-! ### The implicit radius exceeds `R` iff the weighted sum dominates -/

lemma lt_implicitCauchy_iff (n : ℕ) (b : ℕ → ℝ) (hb : ∀ k < n, 0 ≤ b k) {R : ℝ} (hR : 0 < R) :
    R < implicitCauchy n b ↔ 1 < cauchyF n b R := by
  by_cases hne : ∃ k < n, b k ≠ 0
  · obtain ⟨hBpos, hBF, _⟩ := implicitCauchy_spec n b hb hne
    obtain ⟨k0, hk0, hbk0'⟩ := hne
    have hbk0 : 0 < b k0 := lt_of_le_of_ne (hb k0 hk0) (Ne.symm hbk0')
    set B := implicitCauchy n b
    rw [cauchyF_eq] at hBF ⊢
    have hsm := fun {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) =>
      cauchyG_strictMono n b hb k0 hk0 hbk0 hu huv
    constructor
    · intro hRB
      have : B⁻¹ < R⁻¹ := inv_strictAnti₀ hR hRB
      have := hsm (inv_nonneg.mpr hBpos.le) this
      linarith
    · intro h1
      by_contra hle; push Not at hle
      have : R⁻¹ ≤ B⁻¹ := inv_anti₀ hBpos hle
      have := cauchyG_mono n b hb (inv_nonneg.mpr hR.le) this
      linarith
  · push Not at hne
    rw [implicitCauchy_eq_zero n b hne]
    have : cauchyF n b R = 0 := by
      unfold cauchyF
      exact Finset.sum_eq_zero (fun k hk => by rw [hne k (Finset.mem_range.mp hk), zero_mul])
    rw [this]
    constructor <;> intro h <;> linarith

/-! ### Reindexing -/

lemma sum_range_reflect_succ (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ range n, f (n - k) = ∑ j ∈ Ico 1 (n + 1), f j := by
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega,
    ← Finset.sum_range_reflect (fun j => f (1 + j)) n]
  exact Finset.sum_congr rfl (fun k hk => by
    have := Finset.mem_range.mp hk; congr 1; omega)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- `V_R = ∑_{j=2}^n |X_{n-j}| R^{-j}`. -/
noncomputable def tailV (n : ℕ) (X : ℕ → Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  ∑ j ∈ Ico 2 (n + 1), |X (n - j) ω| * (R⁻¹) ^ j

omit [MeasurableSpace Ω] in
lemma weightedSum_eq_tail (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ) (R : ℝ) (ω : Ω) :
    weightedSum n (realCoeff X) R ω = |X (n - 1) ω| * R⁻¹ + tailV n X R ω := by
  rw [weightedSum_eq]
  have h := sum_range_reflect_succ n (fun j => |X (n - j) ω| * (R⁻¹) ^ j)
  have h' : ∑ k ∈ range n, (R⁻¹) ^ (n - k) * ‖realCoeff X k ω‖ =
      ∑ k ∈ range n, |X (n - (n - k)) ω| * (R⁻¹) ^ (n - k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    rw [show n - (n - k) = k by omega]
    simp [realCoeff, mul_comm]
  rw [h', h, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp [tailV]

omit [MeasurableSpace Ω] in
lemma tailV_nonneg (n : ℕ) (X : ℕ → Ω → ℝ) {R : ℝ} (hR : 0 < R) (ω : Ω) : 0 ≤ tailV n X R ω :=
  Finset.sum_nonneg (fun j _ => by positivity)

/-! ### Conditioning on the lower coefficients -/

/-- For `φ` a measurable function of `(X_0, …, X_{n-1})`,
`ℙ{|X_n| < φ} = 𝔼 H(φ)` and `ℙ{|X_n| ≤ φ} = 𝔼 H(φ)`. -/
lemma prob_lead_lt_eq_integral (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Measurable φ) :
    μ.real {ω | |X n ω| < φ (fun k => X k ω)} = ∫ ω, hnCDF (φ (fun k => X k ω)) ∂μ ∧
    μ.real {ω | |X n ω| ≤ φ (fun k => X k ω)} = ∫ ω, hnCDF (φ (fun k => X k ω)) ∂μ := by
  set W : Ω → (Fin n → ℝ) := fun ω k => X k ω
  have hWm : Measurable W := zc_measurable_pi (fun k => hX.measurable (by omega))
  have hXn : IsStdGaussian μ (X n) := hX.gauss n (by omega)
  have hind := hX.indep_init_last.symm
  constructor
  · set S : Set (ℝ × (Fin n → ℝ)) := {p | |p.1| < φ p.2}
    have hS : MeasurableSet S := measurableSet_lt measurable_fst.abs (hφ.comp measurable_snd)
    have := indep_measureReal_eq_integral μ (X n) W hXn.1 hWm hind S hS
    simp only [S, ZeroCert.zc_mem_setOf_eq] at this
    rw [this]
    exact integral_congr_ae (ae_of_all _ (fun ω => hXn.prob_abs_lt μ _))
  · set S : Set (ℝ × (Fin n → ℝ)) := {p | |p.1| ≤ φ p.2}
    have hS : MeasurableSet S := measurableSet_le measurable_fst.abs (hφ.comp measurable_snd)
    have := indep_measureReal_eq_integral μ (X n) W hXn.1 hWm hind S hS
    simp only [S, ZeroCert.zc_mem_setOf_eq] at this
    rw [this]
    exact integral_congr_ae (ae_of_all _ (fun ω => hXn.prob_abs_le μ _))

omit [IsProbabilityMeasure μ] in
lemma integrable_hnCDF_comp (f : Ω → ℝ) (hf : Measurable f) [IsProbabilityMeasure μ] :
    Integrable (fun ω => hnCDF (f ω)) μ :=
  (integrable_const (1 : ℝ)).mono' (hnCDF_continuous.measurable.comp hf).aestronglyMeasurable
    (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnCDF_nonneg _)]; exact hnCDF_le_one _))

/-- `H` is `h₀`-Lipschitz on all of `ℝ`. -/
lemma hnCDF_lipschitz (x y : ℝ) (hxy : x ≤ y) : hnCDF y - hnCDF x ≤ h0 * (y - x) := by
  rcases le_or_gt 0 x with hx | hx
  · exact hnCDF_sub_le hx hxy
  · rw [hnCDF_of_neg hx]
    rcases le_or_gt 0 y with hy | hy
    · have := hnCDF_le_mul y hy
      have := h0_pos
      nlinarith
    · rw [hnCDF_of_neg hy]; have := h0_pos; nlinarith

end ZeroCert

end


-- =====================================================================
-- Part: Tail2
-- =====================================================================

section

/-!
# Section 6.2 (continued): Theorem 6.4 (extreme-root tail and certificate error)
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- **Reversed Rouché step.** If the linear term of the reversed polynomial dominates on
`|w| = R⁻¹`, then `P` has a zero of modulus larger than `R`. -/
lemma exists_large_zero (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hdom : ‖a n‖ + ∑ j ∈ Ico 2 (n + 1), ‖a (n - j)‖ * (R⁻¹) ^ j < ‖a (n - 1)‖ * R⁻¹) :
    ∃ z, peval n a z = 0 ∧ R < ‖z‖ := by
  set c : ℕ → ℂ := fun j => a (n - j)
  obtain ⟨w, hw, hwz⟩ := hRou n c R⁻¹ hn (inv_pos.mpr hR) (by simpa [c] using hdom)
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply han
    have : peval n c 0 = c 0 := by
      unfold peval
      rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [zero_pow hk]) (by simp)]
      simp
    rw [hwz] at this
    simpa [c] using this.symm
  refine ⟨w⁻¹, ?_, ?_⟩
  · have hrefl : peval n a w⁻¹ = (w⁻¹) ^ n * peval n c w := by
      unfold peval
      rw [Finset.mul_sum, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk := Finset.mem_range.mp hk
      simp only [c]
      rw [show n + 1 - 1 - k = n - k by omega]
      have hsplit : (w⁻¹) ^ n = (w⁻¹) ^ (n - k) * (w⁻¹) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ n)]
      rw [hsplit, inv_pow w k]
      field_simp
    rw [hrefl, hwz, mul_zero]
  · rw [norm_inv]
    rw [lt_inv_comm₀ hR (norm_pos_iff.mpr hw0)]
    exact hw

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Extension of a vector `v : Fin n → ℝ` by zero. -/
noncomputable def extV {n : ℕ} (v : Fin n → ℝ) (k : ℕ) : ℝ := if h : k < n then v ⟨k, h⟩ else 0

lemma measurable_extV (n k : ℕ) : Measurable (fun v : Fin n → ℝ => extV v k) := by
  unfold extV
  by_cases h : k < n
  · simp only [h, ZeroCert.zc_dif_pos]; exact measurable_pi_apply _
  · simp only [h, ZeroCert.zc_dif_neg, not_false_eq_true]; exact measurable_const

omit [MeasurableSpace Ω] in
lemma extV_apply {n : ℕ} (X : ℕ → Ω → ℝ) (ω : Ω) {k : ℕ} (hk : k < n) :
    extV (fun i : Fin n => X i ω) k = X k ω := by
  simp [extV, hk]

/-- `(Y/R, V_R)` as measurable functions of `(X_0, …, X_{n-1})`. -/
noncomputable def phiY (n : ℕ) (R : ℝ) (v : Fin n → ℝ) : ℝ := |extV v (n - 1)| * R⁻¹

noncomputable def phiV (n : ℕ) (R : ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Ico 2 (n + 1), |extV v (n - j)| * (R⁻¹) ^ j

lemma measurable_phiY (n : ℕ) (R : ℝ) : Measurable (phiY n R) :=
  (measurable_extV n (n - 1)).abs.mul measurable_const

lemma measurable_phiV (n : ℕ) (R : ℝ) : Measurable (phiV n R) :=
  Finset.measurable_sum _ (fun j _ => (measurable_extV n (n - j)).abs.mul measurable_const)

omit [MeasurableSpace Ω] in
lemma phiY_apply (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    phiY n R (fun i : Fin n => X i ω) = |X (n - 1) ω| * R⁻¹ := by
  simp [phiY, extV_apply X ω (by omega : n - 1 < n)]

omit [MeasurableSpace Ω] in
lemma phiV_apply (n : ℕ) (R : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    phiV n R (fun i : Fin n => X i ω) = tailV n X R ω := by
  unfold phiV tailV
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := Finset.mem_Ico.mp hj
  rw [extV_apply X ω (by omega : n - j < n)]

omit [IsProbabilityMeasure μ] in
/-- `𝔼 V_R = h₀ ∑_{j=2}^n R^{-j}`. -/
lemma integral_tailV (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (R : ℝ) :
    Integrable (tailV n X R) μ ∧ ∫ ω, tailV n X R ω ∂μ = h0 * ∑ j ∈ Ico 2 (n + 1), (R⁻¹) ^ j := by
  have hint : ∀ j ∈ Ico 2 (n + 1), Integrable (fun ω => |X (n - j) ω| * (R⁻¹) ^ j) μ :=
    fun j _ => ((hX.gauss (n - j) (by omega)).integrable_abs μ).mul_const _
  refine ⟨?_, ?_⟩
  · have : tailV n X R = fun ω => ∑ j ∈ Ico 2 (n + 1), |X (n - j) ω| * (R⁻¹) ^ j := rfl
    rw [this]; exact zc_integrable_finset_sum _ hint
  · unfold tailV
    rw [zc_integral_finset_sum _ hint, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_mul_const, (hX.gauss (n - j) (by omega)).integral_abs μ]

/-- `𝔼 H(Y/R) = J(R)`, by the Cauchy law of `X_n / X_{n-1}`. -/
lemma integral_hnCDF_phiY (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    {R : ℝ} (hR : 0 < R) :
    ∫ ω, hnCDF (phiY n R (fun i : Fin n => X i ω)) ∂μ = tailJ R := by
  rw [← (prob_lead_lt_eq_integral μ n X hX (phiY n R) (measurable_phiY n R)).2]
  simp_rw [phiY_apply n hn R X]
  rw [tailJ, ← gaussian_ratio_cauchy μ (n + 1) X hX n (n - 1) (by omega) (by omega) (by omega)
    R⁻¹ (inv_nonneg.mpr hR.le)]
  apply measureReal_congr
  filter_upwards [hX.ae_ne_zero (k := n - 1) (by omega)] with ω hω
  apply propext
  show |X n ω| ≤ |X (n - 1) ω| * R⁻¹ ↔ |X n ω / X (n - 1) ω| ≤ R⁻¹
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hω), mul_comm]

/-- `c_n(R) = 𝔼 H(Y/R + V_R)`. -/
lemma certTail_eq_integral (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) {R : ℝ} (hR : 0 < R) :
    certTail μ n X R = ∫ ω, hnCDF (phiY n R (fun i : Fin n => X i ω) +
      phiV n R (fun i : Fin n => X i ω)) ∂μ := by
  have hφm : Measurable (fun v : Fin n → ℝ => phiY n R v + phiV n R v) := by
    have h1 := measurable_phiY n R
    have h2 := measurable_phiV n R
    fun_prop
  rw [← (prob_lead_lt_eq_integral μ n X hX (fun v => phiY n R v + phiV n R v) hφm).1]
  unfold certTail
  apply measureReal_congr
  filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω
  apply propext
  show R < normImplicitCauchy n X ω ↔ |X n ω| < phiY n R (fun i : Fin n => X i ω) +
      phiV n R (fun i : Fin n => X i ω)
  have hT : 0 < |X n ω| := abs_pos.mpr hω
  rw [phiY_apply n hn, phiV_apply, ← weightedSum_eq_tail n hn X R ω, normImplicitCauchy,
    lt_implicitCauchy_iff n _ (fun k _ => by positivity) hR]
  have : cauchyF n (fun k => |X k ω| / |X n ω|) R = weightedSum n (realCoeff X) R ω / |X n ω| := by
    unfold cauchyF weightedSum cauchyF
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show |X k ω| / |X n ω| * R⁻¹ ^ (n - k) = ‖realCoeff X k ω‖ * R⁻¹ ^ (n - k) / |X n ω|
    rw [show ‖realCoeff X k ω‖ = |X k ω| by simp [realCoeff]]; ring
  rw [this, one_lt_div hT]

/-- `τ_n(R) ≤ c_n(R)`: the implicit Cauchy radius is an outer certificate. -/
lemma rootTail_le_certTail (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (R : ℝ) :
    rootTail μ n (realCoeff X) R ≤ certTail μ n X R := by
  apply measureReal_mono_ae'
  filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω ⟨z, hz, hRz⟩
  show R < normImplicitCauchy n X ω
  by_contra hle; push Not at hle
  have hωc : (X n ω : ℂ) ≠ 0 := by exact_mod_cast hω
  set a : ℕ → ℂ := fun k => realCoeff X k ω / realCoeff X n ω
  have ha : a n = 1 := by simp [a, realCoeff, hωc]
  have hzw := zerosWithin_implicitCauchy n a ha
  have hnorm : (fun k => ‖a k‖) = fun k => |X k ω| / |X n ω| := by
    funext k; simp [a, realCoeff]
  rw [hnorm] at hzw
  have := zerosWithin_of_normalized n (fun k => realCoeff X k ω) _ hzw z hz
  have : ‖z‖ ≤ R := this.trans hle
  linarith

/-- `τ_n(R) ≥ 𝔼 H((Y/R - V_R)_+)` (reversed Rouché). -/
lemma integral_le_rootTail (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) {R : ℝ} (hR : 0 < R) :
    ∫ ω, hnCDF (phiY n R (fun i : Fin n => X i ω) - phiV n R (fun i : Fin n => X i ω)) ∂μ ≤
      rootTail μ n (realCoeff X) R := by
  have hφm : Measurable (fun v : Fin n → ℝ => phiY n R v - phiV n R v) := by
    have h1 := measurable_phiY n R
    have h2 := measurable_phiV n R
    fun_prop
  rw [← (prob_lead_lt_eq_integral μ n X hX (fun v => phiY n R v - phiV n R v) hφm).1]
  apply measureReal_mono_ae'
  filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω hev
  simp only [phiY_apply n hn, phiV_apply] at hev
  apply exists_large_zero hRou n hn (fun k => realCoeff X k ω) (by simpa [realCoeff] using hω) hR
  simp only [realCoeff, Complex.norm_real, Real.norm_eq_abs]
  unfold tailV at hev
  linarith

/-- **Theorem 6.4 (Extreme-root tail and certificate error).** For `n ≥ 1` and `R > 1`,
`J(R) - D_n(R) ≤ τ_n(R) ≤ c_n(R) ≤ J(R) + D_n(R)`, `J(R) ≤ c_n(R)` and
`0 ≤ c_n(R) - τ_n(R) ≤ 2 D_n(R)`. -/
theorem extreme_root_tail (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (R : ℝ) (hR : 1 < R) :
    tailJ R - tailD n R ≤ rootTail μ n (realCoeff X) R ∧
    rootTail μ n (realCoeff X) R ≤ certTail μ n X R ∧
    certTail μ n X R ≤ tailJ R + tailD n R ∧
    tailJ R ≤ certTail μ n X R ∧
    0 ≤ certTail μ n X R - rootTail μ n (realCoeff X) R ∧
    certTail μ n X R - rootTail μ n (realCoeff X) R ≤ 2 * tailD n R := by
  have hR0 : 0 < R := by linarith
  set Yf : Ω → ℝ := fun ω => phiY n R (fun i : Fin n => X i ω)
  set Vf : Ω → ℝ := fun ω => phiV n R (fun i : Fin n => X i ω)
  have hWm : Measurable (fun ω (i : Fin n) => X i ω) :=
    zc_measurable_pi (fun k => hX.measurable (by omega))
  have hYm : Measurable Yf := (measurable_phiY n R).comp hWm
  have hVm : Measurable Vf := (measurable_phiV n R).comp hWm
  have hVeq : Vf = tailV n X R := funext (fun ω => phiV_apply n R X ω)
  obtain ⟨hVint, hVint_eq⟩ := integral_tailV μ n X hX R
  rw [← hVeq] at hVint hVint_eq
  have hD : h0 * ∫ ω, Vf ω ∂μ = tailD n R := by
    rw [hVint_eq, ← mul_assoc, ← sq, h0_sq]; rfl
  have hVnn : ∀ ω, 0 ≤ Vf ω := fun ω => by rw [hVeq]; exact tailV_nonneg n X hR0 ω
  have hJ : ∫ ω, hnCDF (Yf ω) ∂μ = tailJ R := integral_hnCDF_phiY μ n hn X hX hR0
  have hc : certTail μ n X R = ∫ ω, hnCDF (Yf ω + Vf ω) ∂μ := certTail_eq_integral μ n hn X hX hR0
  have hτ1 : ∫ ω, hnCDF (Yf ω - Vf ω) ∂μ ≤ rootTail μ n (realCoeff X) R :=
    integral_le_rootTail μ hRou n hn X hX hR0
  have hτc := rootTail_le_certTail μ n X hX R
  have iY := integrable_hnCDF_comp μ Yf hYm
  have iYp := integrable_hnCDF_comp μ (fun ω => Yf ω + Vf ω) (hYm.add hVm)
  have iYm := integrable_hnCDF_comp μ (fun ω => Yf ω - Vf ω) (hYm.sub hVm)
  have hVi : Integrable (fun ω => h0 * Vf ω) μ := hVint.const_mul h0
  -- upper bound for `c_n`
  have hup : ∫ ω, hnCDF (Yf ω + Vf ω) ∂μ ≤ tailJ R + tailD n R := by
    rw [← hJ, ← hD, ← integral_const_mul, ← integral_add iY hVi]
    exact integral_mono iYp (iY.add hVi) (fun ω => by
      have := hnCDF_lipschitz (Yf ω) (Yf ω + Vf ω) (by linarith [hVnn ω])
      linarith)
  -- lower bound for `τ_n`
  have hlow : tailJ R - tailD n R ≤ ∫ ω, hnCDF (Yf ω - Vf ω) ∂μ := by
    rw [← hJ, ← hD, ← integral_const_mul, ← integral_sub iY hVi]
    exact integral_mono (iY.sub hVi) iYm (fun ω => by
      have := hnCDF_lipschitz (Yf ω - Vf ω) (Yf ω) (by linarith [hVnn ω])
      linarith)
  -- `J ≤ c_n`
  have hJc : tailJ R ≤ ∫ ω, hnCDF (Yf ω + Vf ω) ∂μ := by
    rw [← hJ]
    exact integral_mono iY iYp (fun ω => hnCDF_mono (by linarith [hVnn ω]))
  -- `c_n - τ_n ≤ 2 D_n`
  have hgap : ∫ ω, hnCDF (Yf ω + Vf ω) ∂μ - ∫ ω, hnCDF (Yf ω - Vf ω) ∂μ ≤ 2 * tailD n R := by
    rw [← integral_sub iYp iYm, ← hD, ← mul_assoc, ← integral_const_mul]
    exact integral_mono (iYp.sub iYm) (hVint.const_mul (2 * h0)) (fun ω => by
      have := hnCDF_lipschitz (Yf ω - Vf ω) (Yf ω + Vf ω) (by linarith [hVnn ω])
      linarith)
  rw [hc] at hτc ⊢
  refine ⟨hlow.trans hτ1, hτc, hup, hJc, by linarith, by linarith⟩

/-- Bounds `|R x - 2/π|` for `x ∈ [J(R) - D_n(R), J(R) + D_n(R)]`. -/
lemma abs_R_mul_sub_le (n : ℕ) (hn : 1 ≤ n) {R x : ℝ} (hR : 1 < R)
    (hx1 : tailJ R - tailD n R ≤ x) (hx2 : x ≤ tailJ R + tailD n R) :
    |R * x - 2 / π| ≤ 2 / (π * (R - 1)) + 2 / (3 * π * R ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hRD := R_mul_tailD_le n hn hR
  have hu : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have ha1 := arctan_le_self' hu
  have ha2 := self_sub_cube_le_arctan hu
  have hpi : 0 < 2 / π := by positivity
  have hRJ1 : R * tailJ R ≤ 2 / π := by
    unfold tailJ
    have : R * arctan R⁻¹ ≤ 1 := by
      calc R * arctan R⁻¹ ≤ R * R⁻¹ := mul_le_mul_of_nonneg_left ha1 hR0.le
        _ = 1 := mul_inv_cancel₀ hR0.ne'
    nlinarith
  have hRJ2 : 2 / π - 2 / (3 * π * R ^ 2) ≤ R * tailJ R := by
    unfold tailJ
    have : 1 - 1 / (3 * R ^ 2) ≤ R * arctan R⁻¹ := by
      calc 1 - 1 / (3 * R ^ 2) = R * (R⁻¹ - R⁻¹ ^ 3 / 3) := by field_simp
        _ ≤ R * arctan R⁻¹ := mul_le_mul_of_nonneg_left ha2 hR0.le
    have h2 : 2 / π - 2 / (3 * π * R ^ 2) = 2 / π * (1 - 1 / (3 * R ^ 2)) := by
      field_simp
    rw [h2]
    nlinarith
  have hDn := tailD_nonneg n hR0
  rw [abs_le]
  constructor <;> nlinarith

/-- **Theorem 6.4, uniform statement (6.9).** For every `R > 1`, uniformly in `n ≥ 1`,
`|R τ_n(R) - 2/π| ≤ 2/(π(R-1)) + 2/(3πR²)`, and the same holds for `c_n(R)`. -/
theorem extreme_root_tail_uniform (hRou : RoucheLinear) (X : ℕ → Ω → ℝ) (R : ℝ) (hR : 1 < R) :
    ∀ n, 1 ≤ n → IidStdGaussian μ (n + 1) X →
      |R * rootTail μ n (realCoeff X) R - 2 / π| ≤ 2 / (π * (R - 1)) + 2 / (3 * π * R ^ 2) ∧
      |R * certTail μ n X R - 2 / π| ≤ 2 / (π * (R - 1)) + 2 / (3 * π * R ^ 2) := by
  intro n hn hX
  obtain ⟨h1, h2, h3, h4, -, -⟩ := extreme_root_tail μ hRou n hn X hX R hR
  have hD := tailD_nonneg n (by linarith : (0 : ℝ) < R)
  exact ⟨abs_R_mul_sub_le n hn hR h1 (h2.trans h3),
    abs_R_mul_sub_le n hn hR (by linarith) h3⟩

/-- The uniform bound tends to `0` as `R → ∞`. -/
theorem tail_error_tendsto_zero :
    Tendsto (fun R : ℝ => 2 / (π * (R - 1)) + 2 / (3 * π * R ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => 2 / (π * (R - 1))) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    have : Tendsto (fun R : ℝ => R - 1) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-1) tendsto_id).congr (fun R => by simp [sub_eq_add_neg])
    exact this.const_mul_atTop pi_pos
  have h2 : Tendsto (fun R : ℝ => 2 / (3 * π * R ^ 2)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)
  simpa using h1.add h2

end ZeroCert

end


-- =====================================================================
-- Part: HighConf
-- =====================================================================

section

/-!
# Corollary 6.5: the high-confidence quantile scale
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- The key elementary inequality behind Corollary 6.5: for `R ≥ 5`,
`1/(R+2) < 1/R - 1/(3R³) - 1/(R(R-1))`. -/
lemma highconf_key_ineq {R : ℝ} (hR : 5 ≤ R) :
    1 / (R + 2) < 1 / R - 1 / (3 * R ^ 3) - 1 / (R * (R - 1)) := by
  have hR0 : 0 < R := by linarith
  have hR1 : 0 < R - 1 := by linarith
  have hR2 : 0 < R + 2 := by linarith
  have hexpr : 1 / R - 1 / (3 * R ^ 3) - 1 / (R * (R - 1)) - 1 / (R + 2) =
      (3 * R ^ 2 * (R - 4) - (R - 1) * (R + 2)) / (3 * R ^ 3 * (R - 1) * (R + 2)) := by
    field_simp; ring
  have hnum : 0 < 3 * R ^ 2 * (R - 4) - (R - 1) * (R + 2) := by nlinarith
  have : 0 < 1 / R - 1 / (3 * R ^ 3) - 1 / (R * (R - 1)) - 1 / (R + 2) := by
    rw [hexpr]; positivity
  linarith

lemma tailD_le (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) :
    tailD n R ≤ 2 / π * (1 / (R * (R - 1))) := by
  rw [tailD_eq n hn hR]
  have : 0 ≤ (R⁻¹) ^ (n - 1) := by have : 0 < R := by linarith
                                   positivity
  have hRR : 0 < R * (R - 1) := by nlinarith
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ hRR.le
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The exact confidence radius `r_{n,δ} = inf {R ≥ 0 : ℙ(ρ_z(Q_n) ≤ R) ≥ 1 - δ}`. -/
noncomputable def exactRadius (n : ℕ) (X : ℕ → Ω → ℝ) (δ : ℝ) : ℝ :=
  sInf {R | 0 ≤ R ∧ 1 - δ ≤ containProb μ n (realCoeff X) R}

omit [IsProbabilityMeasure μ] in
lemma containProb_mono (n : ℕ) (A : ℕ → Ω → ℂ) [IsFiniteMeasure μ] {R R' : ℝ} (h : R' ≤ R) :
    containProb μ n A R' ≤ containProb μ n A R :=
  measureReal_mono (fun ω hω z hz => (hω z hz).trans h)

/-- At `R₀ = (2/π)/δ - 2` the true tail already exceeds `δ` (for `δ ≤ 2/(7π)`). -/
lemma rootTail_gt_at_R0 (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 2 / (7 * π)) :
    δ < rootTail μ n (realCoeff X) (2 / (π * δ) - 2) := by
  set c := 2 / π
  have hc : 0 < c := by positivity
  set R0 := 2 / (π * δ) - 2
  have hcδ : 7 ≤ c / δ := by
    rw [le_div_iff₀ hδ0]
    calc 7 * δ ≤ 7 * (2 / (7 * π)) := by linarith
      _ = c := by show 7 * (2 / (7 * π)) = 2 / π; field_simp
  have hR0eq : R0 = c / δ - 2 := by simp only [R0, c]; field_simp
  have hR5 : 5 ≤ R0 := by rw [hR0eq]; linarith
  have hR1 : 1 < R0 := by linarith
  have hR0pos : 0 < R0 := by linarith
  obtain ⟨hlow, -⟩ := extreme_root_tail μ hRou n hn X hX R0 hR1
  have hc' : c ≠ 0 := hc.ne'
  have hδeq : δ = c / (R0 + 2) := by
    rw [hR0eq, sub_add_cancel, div_div_cancel₀ hc']
  have hJ : c * (R0⁻¹ - (R0⁻¹) ^ 3 / 3) ≤ tailJ R0 :=
    mul_le_mul_of_nonneg_left (self_sub_cube_le_arctan (inv_nonneg.mpr hR0pos.le)) hc.le
  have hD := tailD_le n hn hR1
  have key := highconf_key_ineq hR5
  have : c / (R0 + 2) < c * (R0⁻¹ - (R0⁻¹) ^ 3 / 3) - c * (1 / (R0 * (R0 - 1))) := by
    have h1 : R0⁻¹ - (R0⁻¹) ^ 3 / 3 = 1 / R0 - 1 / (3 * R0 ^ 3) := by field_simp
    rw [h1, ← mul_sub, div_eq_mul_one_div c]
    exact mul_lt_mul_of_pos_left key hc
  rw [hδeq]
  linarith

/-- **Corollary 6.5 (High-confidence quantile scale).** For `0 < δ ≤ 2/(7π)` and every `n ≥ 1`,
`2/(πδ) - 2 ≤ r_{n,δ} ≤ 2/(πδ) + 1`. -/
theorem highconfidence_exact (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 2 / (7 * π)) :
    2 / (π * δ) - 2 ≤ exactRadius μ n X δ ∧ exactRadius μ n X δ ≤ 2 / (π * δ) + 1 := by
  set S := {R | 0 ≤ R ∧ 1 - δ ≤ containProb μ n (realCoeff X) R}
  have hmem : 1 + 2 / (π * δ) ∈ S :=
    ⟨by positivity, gaussian_degree_free_radius μ n X hX δ hδ0⟩
  have hbdd : BddBelow S := ⟨0, fun R hR => hR.1⟩
  refine ⟨?_, by rw [add_comm]; exact csInf_le hbdd hmem⟩
  apply le_csInf ⟨_, hmem⟩
  intro R hR
  by_contra hlt; push Not at hlt
  have hτ := rootTail_gt_at_R0 μ hRou n hn X hX δ hδ0 hδ
  have hsum := containProb_add_rootTail μ n (realCoeff X) hX.measurable_realCoeff
    (2 / (π * δ) - 2)
  have hmono := containProb_mono μ n (realCoeff X) hlt.le
  linarith [hR.2]

/-- `𝔼 S_R = h₀ ∑_{j=1}^n R^{-j}` and hence `c_n(R) ≤ (2/π) ∑_{j=1}^n R^{-j} ≤ 2/(π(R-1))`. -/
lemma certTail_le (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    (R : ℝ) (hR : 1 < R) : certTail μ n X R ≤ 2 / (π * (R - 1)) := by
  have hR0 : 0 < R := by linarith
  rw [certTail_eq_integral μ n hn X hX hR0]
  set Sf : Ω → ℝ := fun ω => phiY n R (fun i : Fin n => X i ω) + phiV n R (fun i : Fin n => X i ω)
  have hSeq : ∀ ω, Sf ω = ∑ k ∈ range n, (R⁻¹) ^ (n - k) * |X k ω| := by
    intro ω
    simp only [Sf, phiY_apply n hn, phiV_apply]
    rw [← weightedSum_eq_tail n hn X R ω, weightedSum_eq]
    simp [realCoeff]
  have hint : ∀ k ∈ range n, Integrable (fun ω => (R⁻¹) ^ (n - k) * |X k ω|) μ :=
    fun k hk => ((hX.gauss k (by have := Finset.mem_range.mp hk; omega)).integrable_abs μ).const_mul _
  have hSi : Integrable Sf μ := by
    have : Sf = fun ω => ∑ k ∈ range n, (R⁻¹) ^ (n - k) * |X k ω| := funext hSeq
    rw [this]; exact zc_integrable_finset_sum _ hint
  have hES : ∫ ω, Sf ω ∂μ = h0 * ∑ k ∈ range n, (R⁻¹) ^ (n - k) := by
    simp_rw [hSeq]
    rw [zc_integral_finset_sum _ hint, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [integral_const_mul, (hX.gauss k (by have := Finset.mem_range.mp hk; omega)).integral_abs μ,
      mul_comm]
  have hSnn : ∀ ω, 0 ≤ Sf ω := fun ω => by
    rw [hSeq]; exact Finset.sum_nonneg (fun k _ => by positivity)
  have hWm : Measurable (fun ω (i : Fin n) => X i ω) :=
    zc_measurable_pi (fun k => hX.measurable (by omega))
  calc ∫ ω, hnCDF (Sf ω) ∂μ ≤ ∫ ω, h0 * Sf ω ∂μ :=
        integral_mono (integrable_hnCDF_comp μ Sf (((measurable_phiY n R).comp hWm).add
          ((measurable_phiV n R).comp hWm))) (hSi.const_mul h0)
          (fun ω => hnCDF_le_mul _ (hSnn ω))
    _ = h0 * (h0 * ∑ k ∈ range n, (R⁻¹) ^ (n - k)) := by rw [integral_const_mul, hES]
    _ ≤ h0 * (h0 * (1 / (R - 1))) := by
        have := sum_range_inv_pow_le n hR
        have := h0_pos
        gcongr
    _ = 2 / (π * (R - 1)) := by rw [← mul_assoc, ← sq, h0_sq]; field_simp

/-- `ℙ{B̂_R(Q_n) ≤ R} = 1 - c_n(R)`. -/
lemma certCDF_eq (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    {R : ℝ} (hR : 0 < R) : certCDF μ (normImplicitCauchy n X) R = 1 - certTail μ n X R := by
  have hWm : Measurable (fun ω (i : Fin n) => X i ω) :=
    zc_measurable_pi (fun k => hX.measurable (by omega))
  have hm : MeasurableSet {ω | |X n ω| < phiY n R (fun i : Fin n => X i ω) +
      phiV n R (fun i : Fin n => X i ω)} :=
    measurableSet_lt (hX.measurable (by omega)).abs
      (((measurable_phiY n R).comp hWm).add ((measurable_phiV n R).comp hWm))
  have hae : {ω | R < normImplicitCauchy n X ω} =ᵐ[μ] {ω | |X n ω| <
      phiY n R (fun i : Fin n => X i ω) + phiV n R (fun i : Fin n => X i ω)} := by
    filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω
    apply propext
    show R < normImplicitCauchy n X ω ↔ |X n ω| < phiY n R (fun i : Fin n => X i ω) +
      phiV n R (fun i : Fin n => X i ω)
    have hT : 0 < |X n ω| := abs_pos.mpr hω
    rw [phiY_apply n hn, phiV_apply, ← weightedSum_eq_tail n hn X R ω, normImplicitCauchy,
      lt_implicitCauchy_iff n _ (fun k _ => by positivity) hR]
    have : cauchyF n (fun k => |X k ω| / |X n ω|) R =
        weightedSum n (realCoeff X) R ω / |X n ω| := by
      unfold cauchyF weightedSum cauchyF
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show |X k ω| / |X n ω| * R⁻¹ ^ (n - k) = ‖realCoeff X k ω‖ * R⁻¹ ^ (n - k) / |X n ω|
      rw [show ‖realCoeff X k ω‖ = |X k ω| by simp [realCoeff]]; ring
    rw [this, one_lt_div hT]
  have hnull : NullMeasurableSet {ω | R < normImplicitCauchy n X ω} μ :=
    hm.nullMeasurableSet.congr hae.symm
  have hcompl : {ω | normImplicitCauchy n X ω ≤ R} = {ω | R < normImplicitCauchy n X ω}ᶜ := by
    ext ω; simp
  unfold certCDF certTail
  rw [hcompl, measureReal_compl₀ hnull]
  simp

/-- **Corollary 6.5, certificate quantile.** The same bounds hold for the `(1-δ)`-quantile of the
implicit Cauchy certificate `B̂_R(Q_n)`. -/
theorem highconfidence_certificate (hRou : RoucheLinear) (n : ℕ) (hn : 1 ≤ n)
    (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ 2 / (7 * π)) :
    2 / (π * δ) - 2 ≤ certRadius μ (normImplicitCauchy n X) (1 - δ) ∧
      certRadius μ (normImplicitCauchy n X) (1 - δ) ≤ 2 / (π * δ) + 1 := by
  set B := normImplicitCauchy n X
  set S := {c | 0 ≤ c ∧ 1 - δ ≤ certCDF μ B c}
  have hR1 : 1 < 1 + 2 / (π * δ) := by have : 0 < 2 / (π * δ) := by positivity
                                       linarith
  have hmem : 1 + 2 / (π * δ) ∈ S := by
    refine ⟨by positivity, ?_⟩
    rw [certCDF_eq μ n hn X hX (by linarith)]
    have := certTail_le μ n hn X hX _ hR1
    rw [add_sub_cancel_left, show π * (2 / (π * δ)) = 2 / δ by field_simp, div_div_cancel₀
      (by norm_num : (2 : ℝ) ≠ 0)] at this
    linarith
  have hbdd : BddBelow S := ⟨0, fun R hR => hR.1⟩
  refine ⟨?_, by rw [add_comm]; exact csInf_le hbdd hmem⟩
  apply le_csInf ⟨_, hmem⟩
  intro R hR
  by_contra hlt; push Not at hlt
  have hτ := rootTail_gt_at_R0 μ hRou n hn X hX δ hδ0 hδ
  set R0 := 2 / (π * δ) - 2
  have hR0 : 1 < R0 := by
    have : 7 ≤ 2 / π / δ := by
      rw [le_div_iff₀ hδ0]
      calc 7 * δ ≤ 7 * (2 / (7 * π)) := by linarith
        _ = 2 / π := by field_simp
    have : 2 / π / δ = 2 / (π * δ) := by rw [div_div]
    simp only [R0]; linarith
  obtain ⟨-, hτc, -⟩ := extreme_root_tail μ hRou n hn X hX R0 hR0
  have hcdf : certCDF μ B R ≤ certCDF μ B R0 :=
    measureReal_mono (fun ω hω => le_trans hω hlt.le)
  rw [certCDF_eq μ n hn X hX (R := R0) (by linarith)] at hcdf
  linarith [hR.2]

end ZeroCert

end


-- =====================================================================
-- Part: Annular
-- =====================================================================

section

/-!
# Section 7.1: annular certificates by reversal
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- All zeros lie in the closed annulus `r ≤ |z| ≤ R`. -/
def ZerosInAnnulus (n : ℕ) (a : ℕ → ℂ) (r R : ℝ) : Prop :=
  ∀ z, peval n a z = 0 → r ≤ ‖z‖ ∧ ‖z‖ ≤ R

/-- Reversal: `P^#(w) = w^n P(1/w)`. -/
lemma peval_reverse (n : ℕ) (a : ℕ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    peval n (fun j => a (n - j)) w = w ^ n * peval n a w⁻¹ := by
  unfold peval
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk := Finset.mem_range.mp hk
  try dsimp only
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]
  have hsplit : w ^ n = w ^ (n - k) * w ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ n)]
  rw [hsplit, inv_pow]
  field_simp

lemma peval_zero (n : ℕ) (a : ℕ → ℂ) : peval n a 0 = a 0 := by
  unfold peval
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [zero_pow hk]) (by simp)]
  simp

/-- **Lemma 7.1 (Reversed Cauchy certificate).** If `a_0 ≠ 0` and `|a_k/a_0| ≤ M` for
`1 ≤ k ≤ n`, every zero satisfies `|z| ≥ (1 + M)⁻¹`. -/
theorem reversed_cauchy (hC : CauchyBound) (n : ℕ) (a : ℕ → ℂ) (ha0 : a 0 ≠ 0) (M : ℝ)
    (hM : ∀ k, 1 ≤ k → k ≤ n → ‖a k / a 0‖ ≤ M) (z : ℂ) (hz : peval n a z = 0) :
    (1 + M)⁻¹ ≤ ‖z‖ := by
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [peval_zero] at hz; exact ha0 hz
  set b : ℕ → ℂ := fun j => a (n - j) / a 0
  have hb : b n = 1 := by simp [b, ha0]
  have hbz : peval n b z⁻¹ = 0 := by
    have : peval n b z⁻¹ = (a 0)⁻¹ * peval n (fun j => a (n - j)) z⁻¹ := by
      unfold peval; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by simp only [b]; ring)
    rw [this, peval_reverse n a (inv_ne_zero hz0), inv_inv, hz, mul_zero, mul_zero]
  have hbM : ∀ j < n, ‖b j‖ ≤ M := fun j hj => hM (n - j) (by omega) (by omega)
  have h := hC n b M hb hbM z⁻¹ hbz
  rw [norm_inv] at h
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h1M : 0 < 1 + M := lt_of_lt_of_le (inv_pos.mpr hzn) h
  rw [inv_le_comm₀ h1M hzn]
  exact h

/-- **Lemma 7.1, inner radius form.** `λ_z(P) ≥ (1 + max_{1≤k≤n} |a_k/a_0|)⁻¹`. -/
theorem innerRadius_ge_reversed_cauchy (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ)
    (ha0 : a 0 ≠ 0) (han : a n ≠ 0) (M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ n → ‖a k / a 0‖ ≤ M) :
    (1 + M)⁻¹ ≤ innerRadius n a := by
  obtain ⟨z0, hz0⟩ := zeroSet_nonempty n a hn han
  unfold innerRadius
  refine le_csInf ⟨‖z0‖, z0, hz0, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact reversed_cauchy hC n a ha0 M hM z hz

/-- **Lemma 7.4 (Rouché outer certificate).** If `∑_{k<n} |a_k| R^k < R^n`, then all zeros of the
monic polynomial lie in `|z| < R`. -/
theorem rouche_outer (n : ℕ) (a : ℕ → ℂ) (han : a n = 1) {R : ℝ} (hR : 0 < R)
    (h : ∑ k ∈ range n, ‖a k‖ * R ^ k < R ^ n) (z : ℂ) (hz : peval n a z = 0) : ‖z‖ < R := by
  apply zeros_lt_of_dominance n a hR _ z hz
  rw [han, norm_one]
  have : cauchyF n (fun k => ‖a k‖) R = (∑ k ∈ range n, ‖a k‖ * R ^ k) / R ^ n := by
    unfold cauchyF
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    rw [show R ^ n = R ^ (n - k) * R ^ k by rw [← pow_add, Nat.sub_add_cancel hk.le], inv_pow]
    field_simp
  rw [this, div_lt_one (by positivity)]
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The reversed Gaussian family `X_n, X_{n-1}, …, X_0` is again iid standard Gaussian. -/
lemma IidStdGaussian.reverse {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ (n + 1) X) :
    IidStdGaussian μ (n + 1) (fun k => X (n - k)) where
  gauss k hk := hX.gauss (n - k) (by omega)
  indep := by
    have h := hX.indep.precomp (Fin.rev_injective (n := n + 1))
    convert h using 1
    funext k
    simp only [Fin.val_rev]
    congr 1; omega

/-- Union bound for a family of Cauchy ratios with a common denominator `X_j`. -/
lemma prob_exists_ratio_gt_le (m : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ m X) (j : ℕ)
    (hj : j < m) (s : Finset ℕ) (hs : ∀ k ∈ s, k < m ∧ k ≠ j) (t : ℝ) (ht : 0 ≤ t) :
    μ.real (⋃ k ∈ s, {ω | t < |X k ω / X j ω|}) ≤ s.card * (1 - 2 / π * arctan t) := by
  calc μ.real (⋃ k ∈ s, {ω | t < |X k ω / X j ω|})
      ≤ ∑ k ∈ s, μ.real {ω | t < |X k ω / X j ω|} := measureReal_biUnion_finset_le _ _
    _ = ∑ k ∈ s, (1 - 2 / π * arctan t) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        obtain ⟨hkm, hkj⟩ := hs k hk
        have hmeas : Measurable fun ω => |X k ω / X j ω| :=
          ((hX.measurable hkm).div (hX.measurable hj)).abs
        have hc := gaussian_ratio_cauchy μ m X hX k j hkm hj hkj t ht
        have hcompl : {ω | t < |X k ω / X j ω|} = {ω | |X k ω / X j ω| ≤ t}ᶜ := by
          ext ω; simp
        rw [hcompl, measureReal_compl (measurableSet_le hmeas measurable_const), hc]
        simp
    _ = s.card * (1 - 2 / π * arctan t) := by rw [Finset.sum_const, nsmul_eq_mul]

omit [MeasurableSpace Ω] in
lemma zerosInAnnulus_of_ratios (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (hXn : X n ω ≠ 0) (hX0 : X 0 ω ≠ 0) (r R : ℝ)
    (ho : ∀ k < n, |X k ω / X n ω| ≤ R - 1)
    (hi : ∀ k, 1 ≤ k → k ≤ n → |X k ω / X 0 ω| ≤ 1 / r - 1) :
    ZerosInAnnulus n (fun k => realCoeff X k ω) r R := by
  intro z hz
  have hXnc : (X n ω : ℂ) ≠ 0 := by exact_mod_cast hXn
  have hX0c : (X 0 ω : ℂ) ≠ 0 := by exact_mod_cast hX0
  constructor
  · have := reversed_cauchy hC n (fun k => realCoeff X k ω) hX0c (1 / r - 1) (fun k h1 h2 => by
      simp only [realCoeff, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
      exact hi k h1 h2) z hz
    rwa [add_sub_cancel, one_div, inv_inv] at this
  · apply zerosWithin_of_normalized n (fun k => realCoeff X k ω) R ?_ z hz
    have := hC n (fun k => realCoeff X k ω / realCoeff X n ω) (R - 1)
      (by simp [realCoeff, hXnc]) (fun k hk => by
        simp only [realCoeff, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
        exact ho k hk)
    simpa using this

/-- **Theorem 7.2 (Gaussian annular certificate).** -/
theorem gaussian_annular_union (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (r R : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hR : 1 < R) :
    1 - n * (1 - 2 / π * arctan (R - 1)) - n * (1 - 2 / π * arctan (r⁻¹ - 1)) ≤
      μ.real {ω | ZerosInAnnulus n (fun k => realCoeff X k ω) r R} := by
  set Fo := ⋃ k ∈ range n, {ω | R - 1 < |X k ω / X n ω|}
  set Fi := ⋃ k ∈ Icc 1 n, {ω | r⁻¹ - 1 < |X k ω / X 0 ω|}
  set N := {ω | X n ω = 0} ∪ {ω | X 0 ω = 0}
  have hmeasX : ∀ k ≤ n, Measurable (X k) := fun k hk => hX.measurable (by omega)
  have hFo : MeasurableSet Fo := Finset.measurableSet_biUnion _ (fun k hk =>
    measurableSet_lt measurable_const (((hmeasX k (by
      have := Finset.mem_range.mp hk; omega)).div (hmeasX n le_rfl)).abs))
  have hFi : MeasurableSet Fi := Finset.measurableSet_biUnion _ (fun k hk =>
    measurableSet_lt measurable_const (((hmeasX k (Finset.mem_Icc.mp hk).2).div
      (hmeasX 0 (by omega))).abs))
  have hN : MeasurableSet N := (measurableSet_eq_fun (hmeasX n le_rfl) measurable_const).union
    (measurableSet_eq_fun (hmeasX 0 (by omega)) measurable_const)
  have hNnull : μ.real N = 0 := by
    have h1 := hX.ae_ne_zero (k := n) (by omega)
    have h2 := hX.ae_ne_zero (k := 0) (by omega)
    rw [ae_iff] at h1 h2
    simp only [not_not] at h1 h2
    rw [measureReal_eq_zero_iff]
    exact measure_union_null h1 h2
  have hcov : {ω | ZerosInAnnulus n (fun k => realCoeff X k ω) r R}ᶜ ⊆ Fo ∪ Fi ∪ N := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, Fo, Fi, N, Set.mem_iUnion, ZeroCert.zc_mem_setOf_eq, not_exists,
      not_lt, Finset.mem_range, Finset.mem_Icc] at hcon
    obtain ⟨⟨ho, hi⟩, hXn, hX0⟩ := hcon
    apply hω
    exact zerosInAnnulus_of_ratios hC n X ω hXn hX0 r R ho
      (fun k h1 h2 => by rw [one_div]; exact hi k ⟨h1, h2⟩)
  have h1 := one_sub_le_measureReal μ ((hFo.union hFi).union hN) hcov
  have h2 : μ.real (Fo ∪ Fi ∪ N) ≤ μ.real Fo + μ.real Fi + μ.real N :=
    (measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := μ) Fo Fi])
  have hFo' := prob_exists_ratio_gt_le μ (n + 1) X hX n (by omega) (range n)
    (fun k hk => by have := Finset.mem_range.mp hk; omega) (R - 1) (by linarith)
  have hFi' := prob_exists_ratio_gt_le μ (n + 1) X hX 0 (by omega) (Icc 1 n)
    (fun k hk => by have := Finset.mem_Icc.mp hk; omega) (r⁻¹ - 1)
    (by have : 1 < r⁻¹ := one_lt_inv₀ hr0 |>.mpr hr1
        linarith)
  rw [Finset.card_range] at hFo'
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hFi'
  linarith

/-- **Theorem 7.2, symmetric choice.** With `T = cot(π δ/(4n))`, the annulus
`[(1+T)⁻¹, 1+T]` has probability at least `1 - δ`. -/
theorem gaussian_annular_cot (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {ω | ZerosInAnnulus n (fun k => realCoeff X k ω)
      (1 / (1 + cot (π * δ / (4 * n)))) (1 + cot (π * δ / (4 * n)))} := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set x := π * δ / (4 * n)
  have hx0 : 0 < x := by positivity
  have hx1 : x < π / 2 := by
    simp only [x]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos]
  set T := cot x
  have hT : 0 < T := by
    simp only [T]; rw [cot_eq_cos_div_sin]
    exact div_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hx1⟩)
      (sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos]))
  have h := gaussian_annular_union μ hC n X hX (1 / (1 + T)) (1 + T) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith) (by linarith)
  rw [add_sub_cancel_left, one_div, inv_inv, add_sub_cancel_left, arctan_cot hx0 hx1] at h
  rw [one_div]
  have : 1 - (n : ℝ) * (1 - 2 / π * (π / 2 - x)) - n * (1 - 2 / π * (π / 2 - x)) = 1 - δ := by
    simp only [x]; field_simp; ring
  linarith

/-- **Proposition 7.3 (Exact-marginal annulus).**
`ℙ{r ≤ |ζ| ≤ R ∀ ζ} ≥ max(0, I_n(R-1) + I_n(r⁻¹-1) - 1)`. -/
theorem exact_marginal_annulus (hC : CauchyBound) (n : ℕ) (X : ℕ → Ω → ℝ)
    (hX : IidStdGaussian μ (n + 1) X) (r R : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hR : 1 < R) :
    max 0 (ratioLaw n (R - 1) + ratioLaw n (r⁻¹ - 1) - 1) ≤
      μ.real {ω | ZerosInAnnulus n (fun k => realCoeff X k ω) r R} := by
  apply max_le measureReal_nonneg
  set Eo := {ω | ∀ k < n, |X k ω / X n ω| ≤ R - 1}
  set Ei := {ω | ∀ k < n, |X (n - k) ω / X (n - n) ω| ≤ r⁻¹ - 1}
  have hr' : 1 < r⁻¹ := one_lt_inv₀ hr0 |>.mpr hr1
  have hEo : μ.real Eo = ratioLaw n (R - 1) := ratio_law μ n X hX (R - 1) (by linarith)
  have hEi : μ.real Ei = ratioLaw n (r⁻¹ - 1) :=
    ratio_law μ n (fun k => X (n - k)) (hX.reverse μ) (r⁻¹ - 1) (by linarith)
  have hmeasX : ∀ k ≤ n, Measurable (X k) := fun k hk => hX.measurable (by omega)
  have hEim : MeasurableSet Ei := by
    have : Ei = ⋂ k ∈ range n, {ω | |X (n - k) ω / X (n - n) ω| ≤ r⁻¹ - 1} := by
      ext ω; simp [Ei]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun k _ => measurableSet_le
      (((hmeasX (n - k) (by omega)).div (hmeasX (n - n) (by omega))).abs) measurable_const)
  have hbonf : μ.real Eo + μ.real Ei - 1 ≤ μ.real (Eo ∩ Ei) := by
    have := measureReal_union_add_inter (μ := μ) (s := Eo) hEim
    have := measureReal_le_one (μ := μ) (s := Eo ∪ Ei)
    linarith
  rw [← hEo, ← hEi]
  refine hbonf.trans (measureReal_mono_ae' μ ?_)
  filter_upwards [hX.ae_ne_zero (k := n) (by omega), hX.ae_ne_zero (k := 0) (by omega)]
    with ω hXn hX0 ⟨ho, hi⟩
  apply zerosInAnnulus_of_ratios hC n X ω hXn hX0 r R ho
  intro k h1 h2
  have := hi (n - k) (by omega)
  rw [show n - (n - k) = k by omega, Nat.sub_self, ← one_div] at this
  exact this

/-- **Proposition 7.3, symmetric choice.** With `T = I_n^{-1}(1 - δ/2)`, the annulus
`[(1+T)⁻¹, 1+T]` has probability at least `1 - δ`. -/
theorem exact_marginal_annulus_radius (hC : CauchyBound) (n : ℕ) (hn : 1 ≤ n)
    (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {ω | ZerosInAnnulus n (fun k => realCoeff X k ω)
      (1 + ratioLawInv n (1 - δ / 2))⁻¹ (1 + ratioLawInv n (1 - δ / 2))} := by
  obtain ⟨-, -, -, -, h⟩ := ratioLaw_properties n hn
  obtain ⟨hT0, hTp, -⟩ := h (1 - δ / 2) (by linarith) (by linarith)
  set T := ratioLawInv n (1 - δ / 2)
  by_cases hTz : T = 0
  · -- degenerate case cannot occur: `I_n(0) = 0 ≠ 1 - δ/2`
    exfalso
    rw [hTz, ratioLaw_eq_ratioJ n le_rfl, ratioJ_zero n hn] at hTp
    linarith
  have hTpos : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hTz)
  have h := exact_marginal_annulus μ hC n X hX (1 + T)⁻¹ (1 + T) (by positivity)
    (inv_lt_one_of_one_lt₀ (by linarith)) (by linarith)
  rw [inv_inv, add_sub_cancel_left, hTp] at h
  have : (1 - δ / 2) + (1 - δ / 2) - 1 = 1 - δ := by ring
  rw [this] at h
  exact (le_max_right _ _).trans h

/-- **Proposition 7.3, degree-independent annulus.** With `U_δ = 1 + 4/(πδ)`,
`ℙ{U_δ⁻¹ ≤ |ζ| ≤ U_δ ∀ ζ} ≥ 1 - δ`. -/
theorem degree_free_annulus (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    (δ : ℝ) (hδ0 : 0 < δ) :
    1 - δ ≤ μ.real {ω | ZerosInAnnulus n (fun k => realCoeff X k ω)
      (1 + 4 / (π * δ))⁻¹ (1 + 4 / (π * δ))} := by
  set U := 1 + 4 / (π * δ)
  have hU : 1 < U := by have : 0 < 4 / (π * δ) := by positivity
                        simp only [U]; linarith
  set Y : ℕ → Ω → ℝ := fun k => X (n - k)
  have hY := hX.reverse μ
  have hmeasX : ∀ k ≤ n, Measurable (X k) := fun k hk => hX.measurable (by omega)
  set Fo := {ω | ZerosWithin n (fun k => realCoeff X k ω) U}ᶜ
  set Fi := {ω | ZerosWithin n (fun k => realCoeff Y k ω) U}ᶜ
  set N := {ω | X 0 ω = 0}
  have hFo : MeasurableSet Fo :=
    (measurableSet_zerosWithin n _ hX.measurable_realCoeff U).compl
  have hFi : MeasurableSet Fi :=
    (measurableSet_zerosWithin n _ hY.measurable_realCoeff U).compl
  have hN : MeasurableSet N := measurableSet_eq_fun (hmeasX 0 (by omega)) measurable_const
  have hNnull : μ.real N = 0 := by
    have h1 := hX.ae_ne_zero (k := 0) (by omega)
    rw [ae_iff] at h1; simp only [not_not] at h1
    rw [measureReal_eq_zero_iff]; exact h1
  have htail : ∀ (Z : ℕ → Ω → ℝ), IidStdGaussian μ (n + 1) Z →
      μ.real {ω | ZerosWithin n (fun k => realCoeff Z k ω) U}ᶜ ≤ δ / 2 := by
    intro Z hZ
    have h := (gaussian_degree_free_tail μ n Z hZ U hU)
    have h' : rootTail μ n (realCoeff Z) U ≤ δ / 2 := by
      refine h.1.trans (h.2.trans (le_of_eq ?_))
      simp only [U, add_sub_cancel_left]; field_simp; ring
    have : {ω | ZerosWithin n (fun k => realCoeff Z k ω) U}ᶜ =
        {ω | ∃ z, peval n (fun k => realCoeff Z k ω) z = 0 ∧ U < ‖z‖} := by
      ext ω; simp [ZerosWithin]
    rw [this]; exact h'
  have hcov : {ω | ZerosInAnnulus n (fun k => realCoeff X k ω) U⁻¹ U}ᶜ ⊆ Fo ∪ Fi ∪ N := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, Fo, Fi, N, Set.mem_compl_iff, not_not,
      ZeroCert.zc_mem_setOf_eq] at hcon
    obtain ⟨⟨ho, hi⟩, hX0⟩ := hcon
    apply hω
    intro z hz
    refine ⟨?_, ho z hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [peval_zero] at hz; simp [realCoeff] at hz; exact hX0 hz
    have hrev : peval n (fun k => realCoeff Y k ω) z⁻¹ = 0 := by
      have h := peval_reverse n (fun k => realCoeff X k ω) (inv_ne_zero hz0)
      rw [inv_inv, hz, mul_zero] at h
      exact h
    have := hi z⁻¹ hrev
    rw [norm_inv] at this
    have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [inv_le_comm₀ hzn (by linarith)] at this
    exact this
  have h1 := one_sub_le_measureReal μ ((hFo.union hFi).union hN) hcov
  have h2 : μ.real (Fo ∪ Fi ∪ N) ≤ μ.real Fo + μ.real Fi + μ.real N :=
    (measureReal_union_le _ _).trans (by linarith [measureReal_union_le (μ := μ) Fo Fi])
  have h3 := htail X hX
  have h4 := htail Y hY
  linarith

end ZeroCert

end


-- =====================================================================
-- Part: Chernoff
-- =====================================================================

section

/-!
# Section 7.2: Rouché–Chernoff disk certificates
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The Chernoff bound for a single `λ`. -/
lemma chernoff_single (n : ℕ) (X : ℕ → Ω → ℂ) (hXm : ∀ k < n, Measurable (X k))
    (hind : iIndepFun (fun (k : Fin n) => X k) μ) {R : ℝ} (hR : 0 < R) {l : ℝ} (hl : 0 ≤ l)
    (hint : ∀ k < n, Integrable (fun ω => exp (l * (R ^ k * ‖X k ω‖))) μ) :
    1 - exp (-l * R ^ n) * ∏ k ∈ range n, ∫ ω, exp (l * (R ^ k * ‖X k ω‖)) ∂μ ≤
      containProb μ n (monicCoeff n X) R := by
  set Y : Fin n → Ω → ℝ := fun k ω => R ^ (k : ℕ) * ‖X k ω‖ with hY
  have hYm : ∀ k, Measurable (Y k) := fun k => by
    simp only [hY]; exact (hXm k k.2).norm.const_mul _
  have hYind : iIndepFun Y μ := by
    have := hind.comp (fun (k : Fin n) (z : ℂ) => R ^ (k : ℕ) * ‖z‖)
      (fun k => (measurable_norm).const_mul _)
    exact this
  set S : Ω → ℝ := ∑ k, Y k with hS
  have hSapp : ∀ ω, S ω = ∑ k ∈ range n, ‖X k ω‖ * R ^ k := by
    intro ω
    simp only [hS, Finset.sum_apply, hY]
    rw [Fin.sum_univ_eq_sum_range (fun k => R ^ k * ‖X k ω‖)]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hSm : Measurable S := by
    have : S = fun ω => ∑ k, Y k ω := by ext ω; simp [hS]
    rw [this]; exact Finset.measurable_sum _ (fun k _ => hYm k)
  -- the event `S < R^n` forces containment
  have hsub : {ω | ZerosWithin n (fun k => monicCoeff n X k ω) R}ᶜ ⊆ {ω | R ^ n ≤ S ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, ZeroCert.zc_mem_setOf_eq] at hω ⊢
    by_contra hlt
    push Not at hlt
    apply hω
    intro z hz
    refine (rouche_outer n (fun k => monicCoeff n X k ω) (monicCoeff_self n X ω) hR ?_ z hz).le
    calc ∑ k ∈ range n, ‖monicCoeff n X k ω‖ * R ^ k
        = ∑ k ∈ range n, ‖X k ω‖ * R ^ k := Finset.sum_congr rfl (fun k hk => by
          rw [monicCoeff_of_lt n X ω (Finset.mem_range.mp hk)])
      _ = S ω := (hSapp ω).symm
      _ < R ^ n := hlt
  have h1 := one_sub_le_measureReal μ (measurableSet_le measurable_const hSm) hsub
  have hint' : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable (fun ω => exp (l * Y i ω)) μ :=
    fun i _ => hint i i.2
  have hSint : Integrable (fun ω => exp (l * S ω)) μ :=
    hYind.integrable_exp_mul_sum hYm hint'
  have h2 := measure_ge_le_exp_mul_mgf (μ := μ) (X := S) (R ^ n) hl hSint
  have hmgf : mgf S μ l = ∏ k ∈ range n, ∫ ω, exp (l * (R ^ k * ‖X k ω‖)) ∂μ := by
    simp only [hS]
    rw [hYind.mgf_sum hYm]
    rw [← Fin.prod_univ_eq_prod_range (fun k => ∫ ω, exp (l * (R ^ k * ‖X k ω‖)) ∂μ)]
    rfl
  rw [hmgf] at h2
  unfold containProb
  linarith

/-- **Theorem 7.5 (Chernoff zero certificate).** For independent coefficients with
finite exponential moments `E e^{λ R^k |X_k|} < ∞` for all `λ ∈ (0, λ₀)`,
`Π(R) ≥ 1 - inf_{0<λ<λ₀} e^{-λ R^n} ∏_k E e^{λ R^k |X_k|}`. -/
theorem chernoff_certificate (n : ℕ) (X : ℕ → Ω → ℂ) (hXm : ∀ k < n, Measurable (X k))
    (hind : iIndepFun (fun (k : Fin n) => X k) μ) {R : ℝ} (hR : 0 < R) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hint : ∀ l ∈ Set.Ioo 0 l₀, ∀ k < n, Integrable (fun ω => exp (l * (R ^ k * ‖X k ω‖))) μ) :
    1 - ⨅ l : Set.Ioo 0 l₀, exp (-(l : ℝ) * R ^ n) *
        ∏ k ∈ range n, ∫ ω, exp ((l : ℝ) * (R ^ k * ‖X k ω‖)) ∂μ ≤
      containProb μ n (monicCoeff n X) R := by
  have : Nonempty (Set.Ioo 0 l₀) := ⟨⟨l₀ / 2, by constructor <;> linarith⟩⟩
  have : 1 - containProb μ n (monicCoeff n X) R ≤ ⨅ l : Set.Ioo 0 l₀, exp (-(l : ℝ) * R ^ n) *
        ∏ k ∈ range n, ∫ ω, exp ((l : ℝ) * (R ^ k * ‖X k ω‖)) ∂μ := by
    apply le_ciInf
    intro l
    have := chernoff_single μ n X hXm hind hR l.2.1.le (hint l l.2)
    linarith
  linarith

/-! ## Gaussian moment generating function of `|X|` -/

/-- Standard normal distribution function `Φ`. -/
noncomputable def stdPhi (s : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic s)

/-- Standard normal density `φ`. -/
noncomputable def stdDens (s : ℝ) : ℝ := gaussianPDFReal 0 1 s

lemma integrable_exp_mul_abs_gaussian (s : ℝ) :
    Integrable (fun x => exp (s * |x|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal s).add (integrable_exp_mul_gaussianReal (-s))).mono'
    (by fun_prop) (ae_of_all _ (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; have := exp_pos (-s * x); simp only [Pi.add_apply]; linarith
  · rw [abs_of_nonpos hx]; have := exp_pos (s * x); simp only [Pi.add_apply]
    rw [show s * -x = -s * x by ring]; linarith

/-- `E e^{s|X|} = 2 e^{s²/2} Φ(s)` for `X ~ N(0,1)` (proof of Corollary 7.6). -/
theorem integral_exp_mul_abs_gaussian (s : ℝ) :
    ∫ x, exp (s * |x|) ∂(gaussianReal 0 1) = 2 * exp (s ^ 2 / 2) * stdPhi s := by
  have hpdf : ∀ y, gaussianPDFReal 0 1 y * exp (s * y) =
      exp (s ^ 2 / 2) * gaussianPDFReal s 1 y := by
    intro y
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_comm (exp (s ^ 2 / 2)), mul_assoc, mul_assoc, ← exp_add, ← exp_add]
    congr 2; ring
  have hsymm : ∀ y, gaussianPDFReal 0 1 |y| = gaussianPDFReal 0 1 y := by
    intro y; simp [gaussianPDFReal_def]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have := integral_comp_abs (f := fun y => gaussianPDFReal 0 1 y * exp (s * y))
  simp only [hsymm] at this
  rw [this]
  simp_rw [hpdf]
  rw [integral_const_mul]
  have h1 : ∫ y in Set.Ioi (0 : ℝ), gaussianPDFReal s 1 y = (gaussianReal s 1).real (Set.Ioi 0) := by
    rw [Measure.real, gaussianReal_apply_eq_integral s one_ne_zero, ENNReal.toReal_ofReal]
    exact setIntegral_nonneg measurableSet_Ioi (fun x _ => gaussianPDFReal_nonneg s 1 x)
  have h2 : (gaussianReal s 1).real (Set.Ioi 0) = stdPhi s := by
    have hm : gaussianReal s 1 = (gaussianReal 0 1).map (s - ·) := by
      rw [gaussianReal_map_const_sub]; simp
    rw [hm, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
    have : (fun x => s - x) ⁻¹' Set.Ioi 0 = Set.Iio s := by ext x; simp
    rw [this]
    exact measureReal_congr (Iio_ae_eq_Iic' (ZeroCert.zc_gauss_singleton _))
  rw [h1, h2]; ring

lemma stdPhi_pos (s : ℝ) : 0 < stdPhi s := by
  have h := mgf_pos (μ := gaussianReal 0 1) (X := fun x => |x|) (t := s)
    (integrable_exp_mul_abs_gaussian s)
  rw [mgf, integral_exp_mul_abs_gaussian] at h
  have := exp_pos (s ^ 2 / 2)
  by_contra hle; push Not at hle; nlinarith

lemma stdPhi_hasDerivAt (s : ℝ) : HasDerivAt stdPhi (stdDens s) s := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]; fun_prop
  have hint : ∀ a : ℝ, IntegrableOn (gaussianPDFReal 0 1) (Set.Iic a) :=
    fun a => (integrable_gaussianPDFReal 0 1).integrableOn
  have heq : stdPhi = fun t => stdPhi 0 + ∫ x in (0 : ℝ)..t, gaussianPDFReal 0 1 x := by
    ext t
    unfold stdPhi
    rw [stdGauss_real_apply, stdGauss_real_apply, ← intervalIntegral.integral_Iic_sub_Iic
      (hint 0) (hint t)]
    ring
  rw [heq]
  apply HasDerivAt.const_add
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- **Corollary 7.6 (Gaussian Rouché–Chernoff certificate).** -/
theorem gaussian_chernoff_certificate (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ n X)
    {R : ℝ} (hR : 0 < R) :
    1 - ⨅ l : Set.Ioi (0 : ℝ), exp (-(l : ℝ) * R ^ n) *
        ∏ k ∈ range n, (2 * exp ((l : ℝ) ^ 2 * R ^ (2 * k) / 2) * stdPhi ((l : ℝ) * R ^ k)) ≤
      containProb μ n (monicCoeff n (realCoeff X)) R := by
  have hmom : ∀ l : ℝ, ∀ k < n, ∫ ω, exp (l * (R ^ k * ‖realCoeff X k ω‖)) ∂μ =
      2 * exp (l ^ 2 * R ^ (2 * k) / 2) * stdPhi (l * R ^ k) := by
    intro l k hk
    have hg := hX.gauss k hk
    have : ∀ ω, exp (l * (R ^ k * ‖realCoeff X k ω‖)) = (fun x => exp ((l * R ^ k) * |x|)) (X k ω) := by
      intro ω; simp only [realCoeff, Complex.norm_real, Real.norm_eq_abs]; ring_nf
    rw [integral_congr_ae (ae_of_all _ this), ← integral_map (φ := X k)
      (f := fun x => exp ((l * R ^ k) * |x|)) hg.1.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), hg.2, integral_exp_mul_abs_gaussian]
    congr 2; rw [pow_mul]; ring_nf
  have hint : ∀ l : ℝ, ∀ k < n, Integrable (fun ω => exp (l * (R ^ k * ‖realCoeff X k ω‖))) μ := by
    intro l k hk
    have hg := hX.gauss k hk
    have : (fun ω => exp (l * (R ^ k * ‖realCoeff X k ω‖))) =
        (fun x => exp ((l * R ^ k) * |x|)) ∘ (X k) := by
      ext ω; simp only [Function.comp, realCoeff, Complex.norm_real, Real.norm_eq_abs]; ring_nf
    rw [this]
    refine Integrable.comp_measurable ?_ hg.1
    rw [hg.2]; exact integrable_exp_mul_abs_gaussian _
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hm : ∀ k < n, Measurable (realCoeff X k) := fun k hk =>
    Complex.measurable_ofReal.comp (hX.measurable hk)
  have : 1 - containProb μ n (monicCoeff n (realCoeff X)) R ≤
      ⨅ l : Set.Ioi (0 : ℝ), exp (-(l : ℝ) * R ^ n) *
        ∏ k ∈ range n, (2 * exp ((l : ℝ) ^ 2 * R ^ (2 * k) / 2) * stdPhi ((l : ℝ) * R ^ k)) := by
    apply le_ciInf
    intro l
    have := chernoff_single μ n (realCoeff X) hm (iIndepFun_ofReal hX.indep) hR
      (le_of_lt l.2) (fun k hk => hint l k hk)
    rw [Finset.prod_congr rfl (fun k hk => hmom l k (Finset.mem_range.mp hk))] at this
    linarith
  linarith

end ZeroCert

end


-- =====================================================================
-- Part: Chernoff2
-- =====================================================================

section

/-!
# Section 7.2 (cont.): the normalized logarithmic Chernoff objective `ψ`
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- Cumulant generating function of `|X|`, `X ~ N(0,1)`:
`K(s) = log 2 + s²/2 + log Φ(s)`. -/
noncomputable def absGaussCgf (s : ℝ) : ℝ := log 2 + s ^ 2 / 2 + log (stdPhi s)

/-- Equation (7.1): `ψ(λ) = -λ + ∑_{j=1}^n [log 2 + λ² w_j²/2 + log Φ(λ w_j)]`, `w_j = R^{-j}`. -/
noncomputable def chernoffPsi (R : ℝ) (n : ℕ) (l : ℝ) : ℝ :=
  -l + ∑ j ∈ Icc 1 n, (log 2 + l ^ 2 * ((R ^ j)⁻¹) ^ 2 / 2 + log (stdPhi (l * (R ^ j)⁻¹)))

lemma absGaussCgf_eq_cgf (s : ℝ) :
    absGaussCgf s = cgf (fun x => |x|) (gaussianReal 0 1) s := by
  rw [cgf, mgf, integral_exp_mul_abs_gaussian, log_mul (by have := exp_pos (s ^ 2 / 2); positivity)
    (stdPhi_pos s).ne', log_mul (by norm_num) (exp_pos _).ne', log_exp, absGaussCgf]

lemma absGaussCgf_convex : ConvexOn ℝ Set.univ absGaussCgf := by
  have heq : absGaussCgf = cgf (fun x => |x|) (gaussianReal 0 1) := funext absGaussCgf_eq_cgf
  have hint : interior (integrableExpSet (fun x => |x|) (gaussianReal 0 1)) = Set.univ := by
    have : integrableExpSet (fun x => |x|) (gaussianReal 0 1) = Set.univ := by
      ext s; simp only [integrableExpSet, ZeroCert.zc_mem_setOf_eq, Set.mem_univ, iff_true]
      exact integrable_exp_mul_abs_gaussian s
    rw [this, interior_univ]
  have han : AnalyticOnNhd ℝ (cgf (fun x => |x|) (gaussianReal 0 1)) Set.univ := by
    rw [← hint]; exact analyticOnNhd_cgf
  rw [heq]
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun x => (han x (Set.mem_univ _)).differentiableAt
  · exact fun x => (han.deriv x (Set.mem_univ _)).differentiableAt
  · intro x
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_cgf_eq_integral (by rw [hint]; trivial)]
    apply div_nonneg
    · exact integral_nonneg (fun ω => by positivity)
    · exact (mgf_pos (integrable_exp_mul_abs_gaussian x)).le

lemma convexOn_comp_mul {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun l => f (l * c)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hf.2 (Set.mem_univ (x * c)) (Set.mem_univ (y * c)) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  convert this using 2; ring

lemma convexOn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun l => ∑ i ∈ s, f i l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := ℝ))
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma chernoffPsi_eq (R : ℝ) (n : ℕ) (l : ℝ) :
    chernoffPsi R n l = -l + ∑ j ∈ Icc 1 n, absGaussCgf (l * (R ^ j)⁻¹) := by
  unfold chernoffPsi absGaussCgf
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- `ψ` is convex: a linear term plus log moment generating functions. -/
theorem chernoffPsi_convex (R : ℝ) (n : ℕ) : ConvexOn ℝ Set.univ (chernoffPsi R n) := by
  have : chernoffPsi R n = fun l => -l + ∑ j ∈ Icc 1 n, absGaussCgf (l * (R ^ j)⁻¹) :=
    funext (chernoffPsi_eq R n)
  rw [this]
  refine ConvexOn.add ?_ (convexOn_finset_sum _ _
    (fun j _ => convexOn_comp_mul absGaussCgf_convex _))
  refine ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [smul_eq_mul]; ring

/-- `ψ(0) = 0`, so allowing `λ = 0` includes the trivial bound one. -/
lemma chernoffPsi_zero (R : ℝ) (n : ℕ) : chernoffPsi R n 0 = 0 := by
  have h : stdPhi 0 = 1 / 2 := by
    have := integral_exp_mul_abs_gaussian 0
    simp only [zero_mul, exp_zero, integral_const, probReal_univ, smul_eq_mul,
      mul_one] at this
    norm_num at this; linarith
  simp [chernoffPsi, h, log_inv]

/-- Reindexing `j = n - k`. -/
lemma sum_Icc_one_reflect (n : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ Icc 1 n, g j = ∑ k ∈ range n, g (n - k) := by
  apply Finset.sum_nbij' (fun j => n - j) (fun k => n - k)
  · intro j hj; simp only [mem_Icc, mem_range] at hj ⊢; omega
  · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
  · intro j hj; simp only [mem_Icc] at hj; omega
  · intro k hk; simp only [mem_range] at hk; omega
  · intro j hj; simp only [mem_Icc] at hj; congr 1; omega

/-- **Normalization of the Chernoff bound.** With `λ = λ' R^n`, the Gaussian Chernoff bound
of Corollary 7.6 equals `exp ψ(λ)`. -/
theorem chernoffPsi_normalization {R : ℝ} (hR : 0 < R) (n : ℕ) (l : ℝ) :
    exp (chernoffPsi R n l) = exp (-(l / R ^ n) * R ^ n) *
      ∏ k ∈ range n, (2 * exp ((l / R ^ n) ^ 2 * R ^ (2 * k) / 2) * stdPhi ((l / R ^ n) * R ^ k)) := by
  have hRn : R ^ n ≠ 0 := (pow_pos hR n).ne'
  rw [chernoffPsi, sum_Icc_one_reflect n, exp_add, exp_sum, neg_mul, div_mul_cancel₀ _ hRn]
  congr 1
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hk := Finset.mem_range.mp hk
  have hsplit : R ^ n = R ^ (n - k) * R ^ k := by rw [← pow_add, Nat.sub_add_cancel hk.le]
  have hRk : R ^ k ≠ 0 := (pow_pos hR k).ne'
  have hw : l / R ^ n * R ^ k = l * (R ^ (n - k))⁻¹ := by
    rw [hsplit]; field_simp
  rw [hw, exp_add, exp_add, exp_log (by norm_num), exp_log (stdPhi_pos _)]
  congr 2
  rw [pow_mul, show (l / R ^ n) ^ 2 * (R ^ 2) ^ k = (l / R ^ n * R ^ k) ^ 2 by ring, hw]
  ring_nf

/-- The derivative formula `ψ'(λ) = -1 + ∑_j w_j [λ w_j + φ(λ w_j)/Φ(λ w_j)]`. -/
theorem chernoffPsi_hasDerivAt (R : ℝ) (n : ℕ) (l : ℝ) :
    HasDerivAt (chernoffPsi R n)
      (-1 + ∑ j ∈ Icc 1 n, (R ^ j)⁻¹ * (l * (R ^ j)⁻¹ +
        stdDens (l * (R ^ j)⁻¹) / stdPhi (l * (R ^ j)⁻¹))) l := by
  unfold chernoffPsi
  apply (hasDerivAt_neg l).add
  apply HasDerivAt.fun_sum
  intro j _
  set w := (R ^ j)⁻¹
  have h1 : HasDerivAt (fun l : ℝ => l * w) w l := by simpa using (hasDerivAt_id l).mul_const w
  have h2 : HasDerivAt (fun l : ℝ => stdPhi (l * w)) (stdDens (l * w) * w) l :=
    (stdPhi_hasDerivAt (l * w)).comp (h := fun l : ℝ => l * w) l h1
  have h3 := h2.log (stdPhi_pos _).ne'
  have h4 : HasDerivAt (fun l : ℝ => l ^ 2 * w ^ 2 / 2) (l * w ^ 2) l := by
    have := ((hasDerivAt_pow 2 l).mul_const (w ^ 2)).div_const 2
    convert this using 1; push_cast; ring
  have := ((hasDerivAt_const l (log 2)).add h4).add h3
  convert this using 1
  field_simp
  ring

/-- Tangent-line inequality for differentiable convex functions on `ℝ`. -/
lemma convex_tangent_le {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {x f' : ℝ}
    (hd : HasDerivAt f f' x) (y : ℝ) : f x + f' * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := hf.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) hxy hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hf.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- If `ψ'(0) ≥ 0`, then `ψ ≥ 0` on `[0, ∞)`: the best bound is the trivial one. -/
theorem chernoffPsi_trivial_optimal (R : ℝ) (n : ℕ) {d : ℝ}
    (hd : HasDerivAt (chernoffPsi R n) d 0) (hd0 : 0 ≤ d) {l : ℝ} (hl : 0 ≤ l) :
    0 ≤ chernoffPsi R n l := by
  have := convex_tangent_le (chernoffPsi_convex R n) hd l
  rw [chernoffPsi_zero] at this
  nlinarith

/-- Any critical point of `ψ` is a global minimizer (so the minimizer is found by solving
`ψ'(λ) = 0`). -/
theorem chernoffPsi_critical_isMin (R : ℝ) (n : ℕ) {l₀ : ℝ}
    (hd : HasDerivAt (chernoffPsi R n) 0 l₀) (l : ℝ) :
    chernoffPsi R n l₀ ≤ chernoffPsi R n l := by
  have := convex_tangent_le (chernoffPsi_convex R n) hd l
  linarith

end ZeroCert

end


-- =====================================================================
-- Part: Asymp1
-- =====================================================================

section

/-!
# Section 5: Mills-ratio bounds, the quantiles `b_n`, and tail monotonicity
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- Half-normal tail `H̄(t) = 1 - H(t)`. -/
noncomputable def hnTail (t : ℝ) : ℝ := 1 - hnCDF t

lemma hnTail_pos (t : ℝ) : 0 < hnTail t := by unfold hnTail; linarith [hnCDF_lt_one t]

lemma hnTail_le_one (t : ℝ) : hnTail t ≤ 1 := by unfold hnTail; linarith [hnCDF_nonneg t]

lemma hnTail_continuous : Continuous hnTail := continuous_const.sub hnCDF_continuous

lemma hnTail_hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt hnTail (-hnDens t) t := by
  have h : HasDerivAt (fun x => 1 - hnCDF x) (-hnDens t) t := by
    simpa using (hnCDF_hasDerivAt ht).const_sub 1
  exact h

lemma hnTail_tendsto_zero : Tendsto hnTail atTop (𝓝 0) := by
  have := hnCDF_tendsto_one.const_sub 1
  rw [sub_self] at this
  exact this

lemma hnDens_hasDerivAt (t : ℝ) : HasDerivAt hnDens (-t * hnDens t) t := by
  unfold hnDens
  have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-t) t := by
    have := ((hasDerivAt_pow 2 t).neg).div_const 2
    convert this using 1; push_cast; ring
  have := (h1.exp).const_mul h0
  convert this using 1; ring

lemma hnDens_tendsto_zero : Tendsto hnDens atTop (𝓝 0) := by
  unfold hnDens
  have h : Tendsto (fun t : ℝ => -t ^ 2 / 2) atTop atBot := by
    have : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have := tendsto_neg_atTop_atBot.comp this
    refine this.congr (fun t => ?_); simp [neg_div]
  simpa using (tendsto_exp_atBot.comp h).const_mul h0

/-- A function with nonpositive derivative on `(0,∞)` tending to `0` at infinity is
nonnegative there. -/
lemma nonneg_of_deriv_nonpos_of_tendsto {f f' : ℝ → ℝ}
    (hd : ∀ t > 0, HasDerivAt f (f' t) t) (hneg : ∀ t > 0, f' t ≤ 0)
    (hlim : Tendsto f atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  have hanti : AntitoneOn f (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro x hx; rw [(hd x hx).deriv]; exact hneg x hx
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop t] with s hs
  exact hanti ht (lt_of_lt_of_le ht hs) hs

/-- **Mills-ratio upper bound** `H̄(t) ≤ h(t)/t`. -/
theorem mills_upper {t : ℝ} (ht : 0 < t) : hnTail t ≤ hnDens t / t := by
  have := nonneg_of_deriv_nonpos_of_tendsto (f := fun t => hnDens t / t - hnTail t)
    (f' := fun t => -hnDens t / t ^ 2) (fun s hs => ?_) (fun s hs => ?_) ?_ ht
  · (try simp only at this); linarith
  · have h1 := ((hnDens_hasDerivAt s).div (hasDerivAt_id s) hs.ne').sub (hnTail_hasDerivAt hs)
    convert h1 using 1
    (try simp only [id]); field_simp; ring
  · have := hnDens_pos s; (try simp only); apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · have h1 : Tendsto (fun t => hnDens t / t) atTop (𝓝 0) := by
      have := hnDens_tendsto_zero.mul tendsto_inv_atTop_zero
      simpa [div_eq_mul_inv] using this
    simpa using h1.sub hnTail_tendsto_zero

/-- **Mills-ratio lower bound** `t/(1+t²) h(t) ≤ H̄(t)`. -/
theorem mills_lower {t : ℝ} (ht : 0 < t) : t / (1 + t ^ 2) * hnDens t ≤ hnTail t := by
  have := nonneg_of_deriv_nonpos_of_tendsto (f := fun t => hnTail t - t / (1 + t ^ 2) * hnDens t)
    (f' := fun t => -2 * hnDens t / (1 + t ^ 2) ^ 2) (fun s hs => ?_) (fun s hs => ?_) ?_ ht
  · (try simp only at this); linarith
  · have hq : HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) ((1 - s ^ 2) / (1 + s ^ 2) ^ 2) s := by
      have h2 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
        have := (hasDerivAt_pow 2 s).const_add 1
        convert this using 1; push_cast; ring
      have := (hasDerivAt_id s).div h2 (by positivity)
      convert this using 1; (try simp only [id]); field_simp; ring
    have h1 := (hnTail_hasDerivAt hs).sub (hq.mul (hnDens_hasDerivAt s))
    convert h1 using 1
    field_simp; ring
  · have := hnDens_pos s; (try simp only)
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · have h1 : Tendsto (fun t => t / (1 + t ^ 2) * hnDens t) atTop (𝓝 0) := by
      apply squeeze_zero' (g := hnDens)
      · filter_upwards [eventually_gt_atTop 0] with s hs
        have := hnDens_pos s; positivity
      · filter_upwards [eventually_gt_atTop 0] with s hs
        have := hnDens_pos s
        have : s / (1 + s ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (s - 1)]
        nlinarith
      · exact hnDens_tendsto_zero
    simpa using hnTail_tendsto_zero.sub h1

/-- The hazard function `ℓ(t) = h(t)/H̄(t)` satisfies `ℓ(t) ≥ t`. -/
lemma hazard_ge {t : ℝ} (ht : 0 < t) : t ≤ hnDens t / hnTail t := by
  rw [le_div_iff₀ (hnTail_pos t)]
  have := mills_upper ht
  rw [le_div_iff₀ ht] at this; linarith

/-- `H̄(t) e^{t²/2}` is antitone on `[0, ∞)` (integrated hazard bound). -/
lemma hnTail_mul_exp_antitone : AntitoneOn (fun t => hnTail t * exp (t ^ 2 / 2)) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact (hnTail_continuous.mul (by fun_prop)).continuousOn
  · rw [interior_Ici]; intro x hx
    exact ((hnTail_hasDerivAt hx).mul ((((hasDerivAt_pow 2 x).div_const 2).exp))).differentiableAt
      |>.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    have hx : 0 < x := hx
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      convert this using 1; push_cast; ring
    have hd : HasDerivAt (fun t => hnTail t * exp (t ^ 2 / 2))
        (-hnDens x * exp (x ^ 2 / 2) + hnTail x * (exp (x ^ 2 / 2) * x)) x :=
      (hnTail_hasDerivAt hx).mul h2.exp
    rw [hd.deriv]
    have := mills_upper hx
    rw [le_div_iff₀ hx] at this
    have he := exp_pos (x ^ 2 / 2)
    nlinarith

/-- Ratio bound `H̄(s)/H̄(t) ≤ exp(-(s² - t²)/2)` for `0 ≤ t ≤ s`. -/
lemma hnTail_ratio_le {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    hnTail s ≤ hnTail t * exp (-(s ^ 2 - t ^ 2) / 2) := by
  have := hnTail_mul_exp_antitone ht (ht.trans hts) hts
  try simp only at this
  have he : exp (-(s ^ 2 - t ^ 2) / 2) = exp (t ^ 2 / 2) / exp (s ^ 2 / 2) := by
    rw [← exp_sub]; ring_nf
  rw [he, mul_div_assoc', le_div_iff₀ (exp_pos _)]
  exact this

/-! ## The quantiles `b_n` -/

/-- For continuous monotone `F` with `F 0 < u` attaining `u`, `F (F^{-1}(u)) = u`. -/
lemma apply_lowerQuantile_eq (F : ℝ → ℝ) (hmono : Monotone F) (hcont : Continuous F) (u : ℝ)
    (h0 : F 0 < u) (hne : ∃ t, 0 ≤ t ∧ u ≤ F t) : F (lowerQuantile F u) = u := by
  have hge := le_apply_lowerQuantile F hmono (fun x => hcont.continuousAt.continuousWithinAt) u hne
  apply le_antisymm _ hge
  set q := lowerQuantile F u
  have hlt : ∀ t, 0 ≤ t → t < q → F t < u := by
    intro t ht htq
    by_contra hc; push Not at hc
    have : q ≤ t := csInf_le ⟨0, fun s hs => hs.1⟩ ⟨ht, hc⟩
    linarith
  have hq : 0 < q := by
    rcases (lowerQuantile_nonneg F u).lt_or_eq with h | h
    · exact h
    · exfalso; have h' : q = 0 := h.symm
      rw [h'] at hge; linarith
  have hlim : Tendsto F (𝓝[<] q) (𝓝 (F q)) := hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hq] with t ht
  exact (hlt t ht.1.le ht.2).le

/-- `b_n = H^{-1}(1 - 1/n)`. -/
noncomputable def bn (n : ℕ) : ℝ := lowerQuantile hnCDF (1 - 1 / n)

/-- `a_p = H^{-1}(1 - p)`. -/
noncomputable def ap (p : ℝ) : ℝ := lowerQuantile hnCDF (1 - p)

lemma hnCDF_lowerQuantile {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    hnCDF (lowerQuantile hnCDF u) = u := by
  apply apply_lowerQuantile_eq _ hnCDF_mono hnCDF_continuous u (by rw [hnCDF_zero]; exact hu0)
  obtain ⟨t, ht⟩ := (hnCDF_tendsto_one.eventually (lt_mem_nhds hu1)).exists_forall_of_atTop
  exact ⟨max t 0, le_max_right _ _, (ht _ (le_max_left _ _)).le⟩

lemma lowerQuantile_hnCDF_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < lowerQuantile hnCDF u := by
  rcases (lowerQuantile_nonneg hnCDF u).lt_or_eq with h | h
  · exact h
  · have := hnCDF_lowerQuantile hu0 hu1; rw [← h, hnCDF_zero] at this; linarith

/-- `n H̄(b_n) = 1`. -/
lemma hnTail_bn {n : ℕ} (hn : 2 ≤ n) : hnTail (bn n) = 1 / n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold hnTail bn
  rw [hnCDF_lowerQuantile (by rw [sub_pos, div_lt_one (by linarith)]; linarith)
    (by have : 0 < 1 / (n : ℝ) := by positivity
        linarith)]
  ring

lemma bn_pos {n : ℕ} (hn : 2 ≤ n) : 0 < bn n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact lowerQuantile_hnCDF_pos (by rw [sub_pos, div_lt_one (by linarith)]; linarith)
    (by have : 0 < 1 / (n : ℝ) := by positivity
        linarith)

lemma hnTail_ap {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : hnTail (ap p) = p := by
  unfold hnTail ap; rw [hnCDF_lowerQuantile (by linarith) (by linarith)]; ring

lemma ap_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < ap p :=
  lowerQuantile_hnCDF_pos (by linarith) (by linarith)

/-- `b_n → ∞`. -/
lemma bn_tendsto_atTop : Tendsto bn atTop atTop := by
  rw [tendsto_atTop]
  intro c
  -- choose `N` with `1/N < H̄(max c 0)`
  set c' := max c 0
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / hnTail c')
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hnN : N ≤ n := le_of_max_le_left hn
  by_contra hlt; push Not at hlt
  have h1 : hnTail c' ≤ hnTail (bn n) := by
    unfold hnTail; linarith [hnCDF_mono (show bn n ≤ c' from hlt.le.trans (le_max_left _ _))]
  rw [hnTail_bn hn2] at h1
  have hpos := hnTail_pos c'
  have : (N : ℝ) ≤ n := by exact_mod_cast hnN
  rw [div_lt_iff₀ hpos] at hN
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

end ZeroCert

end


-- =====================================================================
-- Part: Asymp2
-- =====================================================================

section

/-!
# Section 5: Gumbel limit for the normalized Gaussian maximum (distribution function level)

For iid `X_k ~ N(0,1)` and `M_n = max_{k<n} |X_k|`, we have `P{M_n ≤ t} = H(t)^n`, so
`P{G_n ≤ x} = H(b_n + x/b_n)^n =: gumbelF n x` where `G_n = b_n (M_n - b_n)`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace ZeroCert

/-- Distribution function of `G_n = b_n (M_n - b_n)`: `F_n(x) = H(b_n + x/b_n)^n`. -/
noncomputable def gumbelF (n : ℕ) (x : ℝ) : ℝ := hnCDF (bn n + x / bn n) ^ n

lemma bn_inv_tendsto_zero : Tendsto (fun n => (bn n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp bn_tendsto_atTop

/-- `n H̄(b_n + x/b_n) → e^{-x}` (equation (5.4)). -/
theorem tail_ratio_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * hnTail (bn n + x / bn n)) atTop (𝓝 (exp (-x))) := by
  -- continuous envelopes in the variable `y = 1/b_n`
  set U : ℝ → ℝ := fun y => (y ^ 2 + 1) / (1 + x * y ^ 2) * exp (-x - x ^ 2 * y ^ 2 / 2)
  set L : ℝ → ℝ := fun y => (1 + x * y ^ 2) / (y ^ 2 + (1 + x * y ^ 2) ^ 2) *
    exp (-x - x ^ 2 * y ^ 2 / 2)
  have hU : Tendsto (fun n => U (bn n)⁻¹) atTop (𝓝 (exp (-x))) := by
    have hc : ContinuousAt U 0 := by
      simp only [U]
      apply ContinuousAt.mul
      · apply ContinuousAt.div (by fun_prop) (by fun_prop); simp
      · fun_prop
    have := hc.tendsto.comp bn_inv_tendsto_zero
    have h0 : U 0 = exp (-x) := by simp [U]
    rw [h0] at this; exact this
  have hL : Tendsto (fun n => L (bn n)⁻¹) atTop (𝓝 (exp (-x))) := by
    have hc : ContinuousAt L 0 := by
      simp only [L]
      apply ContinuousAt.mul
      · apply ContinuousAt.div (by fun_prop) (by fun_prop); simp
      · fun_prop
    have := hc.tendsto.comp bn_inv_tendsto_zero
    have h0 : L 0 = exp (-x) := by simp [L]
    rw [h0] at this; exact this
  -- eventually `t_n > 0`
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 0 < bn n + x / bn n ∧ 0 < 1 + x * (bn n)⁻¹ ^ 2 := by
    have h1 : Tendsto (fun n => 1 + x * (bn n)⁻¹ ^ 2) atTop (𝓝 1) := by
      have := ((bn_inv_tendsto_zero.pow 2).const_mul x).const_add 1
      simpa using this
    filter_upwards [eventually_ge_atTop 2, h1.eventually (lt_mem_nhds one_pos)] with n hn h
    refine ⟨hn, ?_, h⟩
    have hb : 0 < bn n := bn_pos hn
    have : bn n + x / bn n = bn n * (1 + x * (bn n)⁻¹ ^ 2) := by field_simp
    rw [this]; positivity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [hev] with n ⟨hn, ht, hpos⟩
    set b := bn n
    set t := b + x / b
    have hb : 0 < b := bn_pos hn
    have hnb : (n : ℝ) = 1 / hnTail b := by rw [hnTail_bn hn]; field_simp
    have hlow := mills_lower ht
    have hup := mills_upper hb
    have hexp : hnDens t = hnDens b * exp (-x - x ^ 2 * b⁻¹ ^ 2 / 2) := by
      simp only [hnDens, t]
      rw [mul_assoc, ← exp_add]; congr 2; field_simp; ring
    rw [hnb, one_div, ← div_eq_inv_mul, le_div_iff₀ (hnTail_pos b)]
    calc L b⁻¹ * hnTail b ≤ L b⁻¹ * (hnDens b / b) := by
          apply mul_le_mul_of_nonneg_left hup
          simp only [L]; positivity
      _ = t / (1 + t ^ 2) * hnDens t := by
          rw [hexp]; simp only [L, t]; field_simp
      _ ≤ hnTail t := hlow
  · filter_upwards [hev] with n ⟨hn, ht, hpos⟩
    set b := bn n
    set t := b + x / b
    have hb : 0 < b := bn_pos hn
    have hnb : (n : ℝ) = 1 / hnTail b := by rw [hnTail_bn hn]; field_simp
    have hlow := mills_lower hb
    have hup := mills_upper ht
    have hexp : hnDens t = hnDens b * exp (-x - x ^ 2 * b⁻¹ ^ 2 / 2) := by
      simp only [hnDens, t]
      rw [mul_assoc, ← exp_add]; congr 2; field_simp; ring
    rw [hnb, one_div, ← div_eq_inv_mul, div_le_iff₀ (hnTail_pos b)]
    calc hnTail t ≤ hnDens t / t := hup
      _ = U b⁻¹ * (b / (1 + b ^ 2) * hnDens b) := by
          rw [hexp]; simp only [U, t]; field_simp
      _ ≤ U b⁻¹ * hnTail b := by
          apply mul_le_mul_of_nonneg_left hlow
          simp only [U]; positivity

/-- **Lemma 5.1 (distributional part).** `P{G_n ≤ x} → exp(-e^{-x})`. -/
theorem gumbelF_tendsto (x : ℝ) : Tendsto (fun n => gumbelF n x) atTop (𝓝 (exp (-exp (-x)))) := by
  have h := Real.tendsto_one_add_pow_exp_of_tendsto
    (g := fun n => -hnTail (bn n + x / bn n)) (t := -exp (-x))
    (by simpa using (tail_ratio_tendsto x).neg)
  refine h.congr (fun n => ?_)
  simp [gumbelF, hnTail, sub_eq_add_neg]

/-- **Right tail bound** (5.5): `P{G_n > x} ≤ e^{-x}` for `x ≥ 0`. -/
theorem gumbelF_right_tail {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    1 - gumbelF n x ≤ exp (-x) := by
  set b := bn n
  have hb : 0 < b := bn_pos hn
  set t := b + x / b
  have hbt : b ≤ t := by simp only [t]; have : 0 ≤ x / b := by positivity
                         linarith
  -- Bernoulli: `1 - (1-q)^n ≤ n q`
  have hq0 := hnTail_pos t
  have hq1 := hnTail_le_one t
  have hbern : 1 - gumbelF n x ≤ n * hnTail t := by
    have := one_add_mul_le_pow (a := -hnTail t) (by linarith) n
    simp only [gumbelF, hnTail] at this ⊢
    have h' : hnCDF t = 1 + -(1 - hnCDF t) := by ring
    rw [h']; linarith
  have hratio := hnTail_ratio_le hb.le hbt
  rw [hnTail_bn hn] at hratio
  have hn' : (0 : ℝ) < n := by positivity
  calc 1 - gumbelF n x ≤ n * hnTail t := hbern
    _ ≤ n * (1 / n * exp (-(t ^ 2 - b ^ 2) / 2)) := by gcongr
    _ = exp (-(t ^ 2 - b ^ 2) / 2) := by field_simp
    _ ≤ exp (-x) := by
        apply exp_le_exp.mpr
        have : t ^ 2 - b ^ 2 = 2 * x + x ^ 2 / b ^ 2 := by simp only [t]; field_simp; ring
        rw [this]; have : 0 ≤ x ^ 2 / b ^ 2 := by positivity
        linarith

/-- **Left tail bound** (5.6): `P{G_n ≤ -x} ≤ exp(-e^{x/2})` for `x ≥ 0`. -/
theorem gumbelF_left_tail {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    gumbelF n (-x) ≤ exp (-exp (x / 2)) := by
  set b := bn n
  have hb : 0 < b := bn_pos hn
  set t := b + -x / b
  rcases lt_or_ge t 0 with ht | ht
  · have : gumbelF n (-x) = 0 := by
      simp only [gumbelF]; rw [hnCDF_of_neg ht, zero_pow (by omega)]
    rw [this]; positivity
  · have htb : t ≤ b := by simp only [t]; have : 0 ≤ x / b := by positivity
                           rw [neg_div]; linarith
    have hxb : x ≤ b ^ 2 := by
      simp only [t] at ht
      have : x / b ≤ b := by rw [neg_div] at ht; linarith
      rw [div_le_iff₀ hb] at this; nlinarith
    have hratio := hnTail_ratio_le ht htb
    rw [hnTail_bn hn] at hratio
    have hn' : (0 : ℝ) < n := by positivity
    -- `n H̄(t) ≥ exp((b² - t²)/2) ≥ e^{x/2}`
    have hnq : exp (x / 2) ≤ n * hnTail t := by
      have h1 : 1 ≤ n * (hnTail t * exp (-(b ^ 2 - t ^ 2) / 2)) := by
        calc (1 : ℝ) = n * (1 / n) := by field_simp
          _ ≤ _ := by gcongr
      have h2 : exp (x / 2) ≤ exp ((b ^ 2 - t ^ 2) / 2) := by
        apply exp_le_exp.mpr
        have : b ^ 2 - t ^ 2 = 2 * x - x ^ 2 / b ^ 2 := by simp only [t]; field_simp; ring
        rw [this]
        have : x ^ 2 / b ^ 2 ≤ x := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        linarith
      have h3 : exp (-(b ^ 2 - t ^ 2) / 2) * exp ((b ^ 2 - t ^ 2) / 2) = 1 := by
        rw [← exp_add]; ring_nf; simp
      have h4 : n * hnTail t = n * (hnTail t * exp (-(b ^ 2 - t ^ 2) / 2)) *
          exp ((b ^ 2 - t ^ 2) / 2) := by
        rw [mul_assoc, mul_assoc, h3, mul_one]
      rw [h4]
      have := exp_pos (x / 2)
      nlinarith
    -- `(1 - q)^n ≤ exp(-n q)`
    have hpow : gumbelF n (-x) ≤ exp (-(n * hnTail t)) := by
      simp only [gumbelF]
      have hH : hnCDF t = 1 - hnTail t := by simp [hnTail]
      rw [hH]
      have h1 : 0 ≤ 1 - hnTail t := by simp only [hnTail]; linarith [hnCDF_nonneg t]
      calc (1 - hnTail t) ^ n ≤ (exp (-hnTail t)) ^ n := by
            gcongr
            have := add_one_le_exp (-hnTail t); linarith
        _ = exp (-(n * hnTail t)) := by rw [← exp_nat_mul]; ring_nf
    calc gumbelF n (-x) ≤ exp (-(n * hnTail t)) := hpow
      _ ≤ exp (-exp (x / 2)) := exp_le_exp.mpr (by linarith)

end ZeroCert

end


-- =====================================================================
-- Part: Asymp3
-- =====================================================================

section

/-!
# Section 5: the mean of the Gumbel law is Euler's constant

`E G = ∫_0^∞ (1 - e^{-e^{-x}}) dx - ∫_0^∞ e^{-e^{x}} dx = -Γ'(1) = γ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

/-- `γ = -Γ'(1) = -∫_0^∞ log u e^{-u} du`. -/
lemma eulerMascheroni_eq_integral :
    eulerMascheroniConstant = -∫ u in Ioi (0 : ℝ), log u * exp (-u) := by
  rw [eulerMascheroniConstant_eq_neg_deriv]
  congr 1
  have hC := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
  have hev : Complex.GammaIntegral =ᶠ[𝓝 (1 : ℂ)] Complex.Gamma := by
    have : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hG := (hC.congr_of_eventuallyEq hev.symm).real_of_complex
  have hR : (fun x : ℝ => (Complex.Gamma x).re) = Gamma := by
    funext x; rw [Complex.Gamma_ofReal]; simp
  rw [hR] at hG
  rw [hG.deriv]
  have : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * (↑(log t) * ↑(exp (-t))) =
      ((∫ t : ℝ in Ioi 0, log t * exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp
  rw [this, Complex.ofReal_re]

/-- Substitution `u = e^{-x}`. -/
lemma integral_log_mul_exp_neg :
    ∫ u in Ioi (0 : ℝ), log u * exp (-u) = ∫ x : ℝ, -(x * exp (-x) * exp (-exp (-x))) := by
  have himg : (fun x : ℝ => exp (-x)) '' univ = Ioi 0 := by
    rw [image_univ]
    ext u; simp only [mem_range, mem_Ioi]
    constructor
    · rintro ⟨x, rfl⟩; exact exp_pos _
    · intro hu; exact ⟨-log u, by simp [exp_log hu]⟩
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := fun x : ℝ => exp (-x))
    (f' := fun x => -exp (-x)) MeasurableSet.univ
    (fun x _ => by
      have := (hasDerivAt_neg x).exp
      exact (by simpa using this : HasDerivAt (fun x : ℝ => exp (-x)) (-exp (-x)) x).hasDerivWithinAt)
    (fun x _ y _ hxy => by simpa using hxy) (fun u => log u * exp (-u))
  rw [himg] at h
  rw [h, Measure.restrict_univ]
  congr 1; funext x
  simp only [abs_neg, abs_of_pos (exp_pos _), log_exp, smul_eq_mul]
  ring

lemma integrableOn_mul_exp_neg_Ioi : IntegrableOn (fun x : ℝ => x * exp (-x)) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  norm_num; ring

lemma one_sub_exp_neg_exp_neg_le {x : ℝ} : |exp (-exp (-x)) - 1| ≤ exp (-x) := by
  have h1 : exp (-exp (-x)) ≤ 1 := by rw [exp_le_one_iff]; simp; positivity
  have h2 := add_one_le_exp (-exp (-x))
  rw [abs_of_nonpos (by linarith)]; linarith

lemma exp_neg_exp_le (x : ℝ) : exp (-exp x) ≤ exp (-x) := by
  apply exp_le_exp.mpr; have := add_one_le_exp x; linarith

lemma two_mul_le_exp (x : ℝ) : 2 * x ≤ exp x := by
  rcases le_total 0 x with hx | hx
  · have := Real.quadratic_le_exp_of_nonneg hx
    nlinarith [sq_nonneg (x - 1)]
  · have := exp_pos x; linarith

lemma exp_neg_exp_le_two (x : ℝ) : exp (-exp x) ≤ exp (-(2 * x)) := by
  apply exp_le_exp.mpr; have := two_mul_le_exp x; linarith

lemma integrableOn_one_sub_gumbel : IntegrableOn (fun x : ℝ => 1 - exp (-exp (-x))) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 one_pos).mono' (by fun_prop : Continuous _).aestronglyMeasurable
    (ae_of_all _ (fun x => ?_))
  rw [Real.norm_eq_abs, abs_sub_comm, neg_mul, one_mul]; exact one_sub_exp_neg_exp_neg_le

lemma integrableOn_exp_neg_exp : IntegrableOn (fun x : ℝ => exp (-exp x)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 one_pos).mono' (by fun_prop : Continuous _).aestronglyMeasurable
    (ae_of_all _ (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), neg_mul, one_mul]; exact exp_neg_exp_le x

/-- Integration by parts on `(0, ∞)` for the right half. -/
lemma gumbel_A_part : ∫ x in Ioi (0 : ℝ), x * (exp (-x) * exp (-exp (-x))) =
    ∫ x in Ioi (0 : ℝ), (1 - exp (-exp (-x))) := by
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => exp (-exp (-x)) - 1)
      (exp (-x) * exp (-exp (-x))) x := by
    intro x _
    have h1 := ((hasDerivAt_neg x).exp.neg).exp
    have := h1.sub_const 1
    convert this using 1; simp; ring
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x) 1 x := fun x _ => hasDerivAt_id x
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv (a' := 0) (b' := 0) ?_ ?_ ?_ ?_
  · rw [h]
    simp only [one_mul, sub_zero, zero_sub]
    rw [← integral_neg]; congr 1; funext x; ring
  · refine integrableOn_mul_exp_neg_Ioi.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ =>
        x * (exp (-x) * exp (-exp (-x)))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      have hx : 0 < x := hx
      simp only [Pi.mul_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have h1 : exp (-exp (-x)) ≤ 1 := by rw [exp_le_one_iff]; simp; positivity
      have h2 := exp_pos (-x)
      have h3 : exp (-x) * exp (-exp (-x)) ≤ exp (-x) := by nlinarith
      exact mul_le_mul_of_nonneg_left h3 hx.le
  · refine (exp_neg_integrableOn_Ioi 0 one_pos).mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => 1 * (exp (-exp (-x)) - 1)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      simp only [Pi.mul_apply, Real.norm_eq_abs, one_mul, neg_mul]
      exact one_sub_exp_neg_exp_neg_le
  · have hc : Continuous (fun x : ℝ => x * (exp (-exp (-x)) - 1)) := by fun_prop
    have := hc.tendsto 0
    simp at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simp only [pow_one] at h0
    apply squeeze_zero_norm' _ h0
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left one_sub_exp_neg_exp_neg_le hx

/-- Integration by parts on `(0, ∞)` for the reflected left half. -/
lemma gumbel_B_part : ∫ x in Ioi (0 : ℝ), x * (exp x * exp (-exp x)) =
    ∫ x in Ioi (0 : ℝ), exp (-exp x) := by
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => -exp (-exp x)) (exp x * exp (-exp x)) x := by
    intro x _
    have h0 : HasDerivAt (fun x => -exp x) (-exp x) x := (hasDerivAt_exp x).neg
    have h1 := h0.exp.neg
    convert h1 using 1; ring
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x) 1 x := fun x _ => hasDerivAt_id x
  have hb : ∀ x : ℝ, 0 ≤ x → x * (exp x * exp (-exp x)) ≤ x * exp (-x) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ hx
    have := exp_neg_exp_le_two x
    calc exp x * exp (-exp x) ≤ exp x * exp (-(2 * x)) := by gcongr
      _ = exp (-x) := by rw [← exp_add]; ring_nf
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv (a' := 0) (b' := 0) ?_ ?_ ?_ ?_
  · rw [h]
    simp only [one_mul, sub_zero, zero_sub, integral_neg, neg_neg]
  · refine integrableOn_mul_exp_neg_Ioi.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => x * (exp x * exp (-exp x))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      have hx : 0 < x := hx
      simp only [Pi.mul_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact hb x hx.le
  · have := integrableOn_exp_neg_exp.neg
    exact IntegrableOn.congr_fun this (fun x _ => by simp) measurableSet_Ioi
  · have hc : Continuous (fun x : ℝ => x * -exp (-exp x)) := by fun_prop
    convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 2
    simp
  · have h0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simp only [pow_one] at h0
    apply squeeze_zero_norm' _ h0
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx, abs_neg,
      abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (exp_neg_exp_le x) hx

/-- **Mean of the Gumbel law.**
`∫_0^∞ (1 - e^{-e^{-x}}) dx - ∫_0^∞ e^{-e^{x}} dx = γ`. -/
theorem gumbel_mean_eq_eulerMascheroni :
    (∫ x in Ioi (0 : ℝ), (1 - exp (-exp (-x)))) - ∫ x in Ioi (0 : ℝ), exp (-exp x) =
      eulerMascheroniConstant := by
  rw [eulerMascheroni_eq_integral, integral_log_mul_exp_neg, integral_neg, neg_neg]
  set f : ℝ → ℝ := fun x => x * exp (-x) * exp (-exp (-x))
  have hIoi : IntegrableOn f (Ioi 0) := by
    refine integrableOn_mul_exp_neg_Ioi.mono' (by fun_prop : Continuous f).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
    have hx : 0 < x := hx
    simp only [f, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have h1 : exp (-exp (-x)) ≤ 1 := by rw [exp_le_one_iff]; simp; positivity
    have h2 : 0 < x * exp (-x) := by positivity
    nlinarith
  have hrefl : ∀ x, f (-x) = -(x * (exp x * exp (-exp x))) := by
    intro x; simp only [f, neg_neg]; ring
  have hIic : IntegrableOn f (Iic 0) := by
    have hB : IntegrableOn (fun x : ℝ => x * (exp x * exp (-exp x))) (Ioi 0) := by
      refine integrableOn_mul_exp_neg_Ioi.mono' (by fun_prop : Continuous _).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      have hx : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ hx.le
      calc exp x * exp (-exp x) ≤ exp x * exp (-(2 * x)) := by gcongr; exact two_mul_le_exp x
        _ = exp (-x) := by rw [← exp_add]; ring_nf
    have : IntegrableOn (fun x => f (-x)) (Ioi 0) :=
      IntegrableOn.congr_fun hB.neg (fun x _ => (hrefl x).symm) measurableSet_Ioi
    have h2 := this.comp_neg
    simp only [neg_neg, neg_Ioi, neg_zero] at h2
    exact (h2.mono_set (fun x hx => hx) : IntegrableOn f (Iio 0)) |>.congr_set_ae
      Iio_ae_eq_Iic.symm
  have hsplit : ∫ x, f x = (∫ x in Iic 0, f x) + ∫ x in Ioi 0, f x := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hIic hIoi,
      Iic_union_Ioi, Measure.restrict_univ]
  have hleft : ∫ x in Iic (0 : ℝ), f x = -∫ x in Ioi (0 : ℝ), exp (-exp x) := by
    rw [← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
    simp_rw [hrefl]
    rw [integral_neg, gumbel_B_part]
  have hright : ∫ x in Ioi (0 : ℝ), f x = ∫ x in Ioi (0 : ℝ), (1 - exp (-exp (-x))) := by
    rw [← gumbel_A_part]; congr 1; funext x; simp only [f]; ring
  rw [hsplit, hleft, hright]; ring

end ZeroCert

end


-- =====================================================================
-- Part: Asymp4
-- =====================================================================

section

/-!
# Section 5: convergence of the tail-integral mean of `G_n` to `γ`
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

lemma gumbelF_continuous (n : ℕ) : Continuous (gumbelF n) := by
  unfold gumbelF
  exact (hnCDF_continuous.comp (continuous_const.add (continuous_id.div_const _))).pow n

lemma gumbelF_nonneg (n : ℕ) (x : ℝ) : 0 ≤ gumbelF n x := pow_nonneg (hnCDF_nonneg _) n

lemma gumbelF_le_one (n : ℕ) (x : ℝ) : gumbelF n x ≤ 1 :=
  pow_le_one₀ (hnCDF_nonneg _) (hnCDF_le_one _)

lemma exp_neg_exp_half_le (x : ℝ) : exp (-exp (x / 2)) ≤ exp (-(x / 2)) := exp_neg_exp_le _

/-- The tail-integral form of the mean of `G_n`:
`∫_0^∞ P{G_n > x} dx - ∫_0^∞ P{G_n < -x} dx`. -/
noncomputable def gumbelTailMean (n : ℕ) : ℝ :=
  (∫ x in Ioi (0 : ℝ), (1 - gumbelF n x)) - ∫ x in Ioi (0 : ℝ), gumbelF n (-x)

lemma integrableOn_exp_neg_half : IntegrableOn (fun x : ℝ => exp (-(x / 2))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 1 / 2 by norm_num)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  ring_nf

lemma integrableOn_one_sub_gumbelF {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun x => 1 - gumbelF n x) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 one_pos).mono'
    ((continuous_const.sub (gumbelF_continuous n)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [gumbelF_le_one n x]), neg_mul, one_mul]
  exact gumbelF_right_tail hn (le_of_lt hx)

lemma integrableOn_gumbelF_neg {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun x => gumbelF n (-x)) (Ioi 0) := by
  refine integrableOn_exp_neg_half.mono'
    (((gumbelF_continuous n).comp continuous_neg).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (gumbelF_nonneg _ _)]
  exact (gumbelF_left_tail hn (le_of_lt hx)).trans (exp_neg_exp_half_le x)

/-- **Lemma 5.1 (mean).** The tail-integral mean of `G_n` converges to `γ`. -/
theorem gumbelTailMean_tendsto :
    Tendsto gumbelTailMean atTop (𝓝 eulerMascheroniConstant) := by
  rw [← gumbel_mean_eq_eulerMascheroni]
  apply Tendsto.sub
  · apply tendsto_integral_filter_of_dominated_convergence (fun x => exp (-1 * x))
    · exact Eventually.of_forall
        (fun n => (continuous_const.sub (gumbelF_continuous n)).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [gumbelF_le_one n x]), neg_mul, one_mul]
      exact gumbelF_right_tail hn (le_of_lt hx)
    · exact exp_neg_integrableOn_Ioi 0 one_pos
    · exact ae_of_all _ (fun x => (gumbelF_tendsto x).const_sub 1)
  · apply tendsto_integral_filter_of_dominated_convergence (fun x => exp (-(x / 2)))
    · exact Eventually.of_forall
        (fun n => ((gumbelF_continuous n).comp continuous_neg).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (gumbelF_nonneg _ _)]
      exact (gumbelF_left_tail hn (le_of_lt hx)).trans (exp_neg_exp_half_le x)
    · exact integrableOn_exp_neg_half
    · refine ae_of_all _ (fun x => ?_)
      have := gumbelF_tendsto (-x)
      simpa using this

end ZeroCert

end


-- =====================================================================
-- Part: Asymp5
-- =====================================================================

section

/-!
# Section 5: the Gaussian maximum `M_n` and the normalized maximum `G_n` as random variables
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

variable {Ω : Type*}

/-- `M_n = max_{k<n} |X_k|` (with `M_0 = 0`). -/
noncomputable def maxAbs (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => max (maxAbs X n ω) |X n ω|

lemma maxAbs_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ maxAbs X n ω := by
  induction n with
  | zero => simp [maxAbs]
  | succ n ih => simp only [maxAbs]; exact le_max_of_le_left ih

lemma maxAbs_le_iff (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    maxAbs X n ω ≤ t ↔ ∀ k < n, |X k ω| ≤ t := by
  induction n with
  | zero => simp [maxAbs, ht]
  | succ n ih =>
    simp only [maxAbs, max_le_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact h1 k h
      · exact h2
    · intro h; exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

lemma maxAbs_lt_iff (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {t : ℝ} (ht : 0 < t) :
    maxAbs X n ω < t ↔ ∀ k < n, |X k ω| < t := by
  induction n with
  | zero => simp [maxAbs, ht]
  | succ n ih =>
    simp only [maxAbs, max_lt_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact h1 k h
      · exact h2
    · intro h; exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

lemma maxAbs_le_sum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxAbs X n ω ≤ ∑ k ∈ Finset.range n, |X k ω| := by
  induction n with
  | zero => simp [maxAbs]
  | succ n ih =>
    simp only [maxAbs, Finset.sum_range_succ]
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, |X k ω| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg _)
    exact max_le (by linarith [abs_nonneg (X n ω)]) (by linarith)

lemma maxAbs_sq_le_sum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    maxAbs X n ω ^ 2 ≤ ∑ k ∈ Finset.range n, X k ω ^ 2 := by
  induction n with
  | zero => simp [maxAbs]
  | succ n ih =>
    simp only [maxAbs, Finset.sum_range_succ]
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, X k ω ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rcases le_total (maxAbs X n ω) |X n ω| with h | h
    · rw [max_eq_right h, sq_abs]; linarith
    · rw [max_eq_left h]; nlinarith [sq_nonneg (X n ω)]

variable [MeasurableSpace Ω]

lemma maxAbs_measurable (X : ℕ → Ω → ℝ) (n : ℕ) (hX : ∀ k < n, Measurable (X k)) :
    Measurable (maxAbs X n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih (fun k hk => hX k (by omega))).max (hX n (by omega)).abs

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- `P{M_n ≤ t} = H(t)^n` for `t ≥ 0`. -/
lemma prob_maxAbs_le {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | maxAbs X n ω ≤ t} = hnCDF t ^ n := by
  rw [← hX.prob_all_abs_le t]
  congr 1; ext ω; exact maxAbs_le_iff X n ω ht

omit [IsProbabilityMeasure μ] in
/-- `P{M_n < t} = H(t)^n` for `t > 0`. -/
lemma prob_maxAbs_lt {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | maxAbs X n ω < t} = hnCDF t ^ n := by
  have := prob_forall_fin_eq_prod_real n X hX.indep (fun _ => Set.Ioo (-t) t)
    (fun _ => measurableSet_Ioo)
  simp only [Set.mem_Ioo, ← abs_lt] at this
  have hset : {ω | maxAbs X n ω < t} = {ω | ∀ k < n, |X k ω| < t} := by
    ext ω; exact maxAbs_lt_iff X n ω ht
  rw [hset, this, Finset.prod_congr rfl (fun k hk =>
    (hX.gauss k (Finset.mem_range.mp hk)).prob_abs_lt μ t)]
  simp

/-- The normalized maximum `G_n = b_n (M_n - b_n)`. -/
noncomputable def gumbelG (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := bn n * (maxAbs X n ω - bn n)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma gumbelG_le_iff {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 2 ≤ n) (ω : Ω) (x : ℝ) :
    gumbelG X n ω ≤ x ↔ maxAbs X n ω ≤ bn n + x / bn n := by
  have hb := bn_pos hn
  unfold gumbelG
  rw [← sub_le_iff_le_add', le_div_iff₀ hb, mul_comm]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma gumbelG_lt_iff {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 2 ≤ n) (ω : Ω) (x : ℝ) :
    gumbelG X n ω < x ↔ maxAbs X n ω < bn n + x / bn n := by
  have hb := bn_pos hn
  unfold gumbelG
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ hb, mul_comm]

/-- `P{G_n ≤ x} = F_n(x)`. -/
lemma prob_gumbelG_le {n : ℕ} (hn : 2 ≤ n) {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) (x : ℝ) :
    μ.real {ω | gumbelG X n ω ≤ x} = gumbelF n x := by
  simp_rw [gumbelG_le_iff hn]
  rcases le_or_gt 0 (bn n + x / bn n) with ht | ht
  · exact prob_maxAbs_le μ hX ht
  · have : {ω | maxAbs X n ω ≤ bn n + x / bn n} = ∅ := by
      ext ω; simp only [ZeroCert.zc_mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (maxAbs_nonneg X n ω)
    rw [this, measureReal_empty, gumbelF, hnCDF_of_neg ht, zero_pow (by omega)]

omit [IsProbabilityMeasure μ] in
/-- `P{G_n < x} = F_n(x)`. -/
lemma prob_gumbelG_lt {n : ℕ} (hn : 2 ≤ n) {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) (x : ℝ) :
    μ.real {ω | gumbelG X n ω < x} = gumbelF n x := by
  simp_rw [gumbelG_lt_iff hn]
  rcases lt_or_ge 0 (bn n + x / bn n) with ht | ht
  · exact prob_maxAbs_lt μ hX ht
  · have : {ω | maxAbs X n ω < bn n + x / bn n} = ∅ := by
      ext ω; simp only [ZeroCert.zc_mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact ht.trans (maxAbs_nonneg X n ω)
    rw [this, measureReal_empty, gumbelF]
    rcases ht.lt_or_eq with h | h
    · rw [hnCDF_of_neg h, zero_pow (by omega)]
    · rw [h, hnCDF_zero, zero_pow (by omega)]

omit [IsProbabilityMeasure μ] in
lemma gumbelG_measurable {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    Measurable (gumbelG X n) := by
  unfold gumbelG
  exact measurable_const.mul ((maxAbs_measurable X n (fun k hk => hX.measurable hk)).sub
    measurable_const)

omit [IsProbabilityMeasure μ] in
lemma IsStdGaussian.integrable_sq {X : Ω → ℝ} (hX : IsStdGaussian μ X) :
    Integrable (fun ω => X ω ^ 2) μ := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  rw [← hX.2] at h
  have := h.comp_measurable hX.1
  simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using this

omit [IsProbabilityMeasure μ] in
lemma maxAbs_integrable {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    Integrable (maxAbs X n) μ := by
  refine (zc_integrable_finset_sum (Finset.range n) (fun k hk =>
    ((hX.gauss k (Finset.mem_range.mp hk)).integrable_abs μ))).mono'
    (maxAbs_measurable X n (fun k hk => hX.measurable hk)).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (maxAbs_nonneg X n ω)]
  simpa using maxAbs_le_sum X n ω

omit [IsProbabilityMeasure μ] in
lemma maxAbs_sq_integrable {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    Integrable (fun ω => maxAbs X n ω ^ 2) μ := by
  refine (zc_integrable_finset_sum (Finset.range n) (fun k hk =>
    ((hX.gauss k (Finset.mem_range.mp hk)).integrable_sq μ))).mono'
    ((maxAbs_measurable X n (fun k hk => hX.measurable hk)).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa using maxAbs_sq_le_sum X n ω

lemma gumbelG_integrable {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    Integrable (gumbelG X n) μ := by
  unfold gumbelG
  exact ((maxAbs_integrable μ hX).sub (integrable_const _)).const_mul _

lemma gumbelG_sq_integrable {n : ℕ} {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    Integrable (fun ω => gumbelG X n ω ^ 2) μ := by
  have : (fun ω => gumbelG X n ω ^ 2) = fun ω => bn n ^ 2 * (maxAbs X n ω ^ 2 -
      2 * bn n * maxAbs X n ω + bn n ^ 2) := by
    funext ω; unfold gumbelG; ring
  rw [this]
  exact (((maxAbs_sq_integrable μ hX).sub ((maxAbs_integrable μ hX).const_mul _)).add
    (integrable_const _)).const_mul _

/-- **Lemma 5.1 (mean, random-variable form).** `E G_n = ∫_0^∞ P{G_n > x} dx - ∫_0^∞ P{G_n<-x} dx`. -/
theorem integral_gumbelG {n : ℕ} (hn : 2 ≤ n) {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    ∫ ω, gumbelG X n ω ∂μ = gumbelTailMean n := by
  set G := gumbelG X n
  have hGm := gumbelG_measurable μ hX
  have hGi := gumbelG_integrable μ hX
  have hpos : Integrable (fun ω => max (G ω) 0) μ := hGi.pos_part
  have hneg : Integrable (fun ω => max (-G ω) 0) μ := hGi.neg_part
  have hsplit : ∫ ω, G ω ∂μ = (∫ ω, max (G ω) 0 ∂μ) - ∫ ω, max (-G ω) 0 ∂μ := by
    rw [← integral_sub hpos hneg]; congr 1; funext ω
    rcases le_total 0 (G ω) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rw [hsplit, hpos.integral_eq_integral_meas_lt (ae_of_all _ (fun ω => le_max_right _ _)),
    hneg.integral_eq_integral_meas_lt (ae_of_all _ (fun ω => le_max_right _ _))]
  unfold gumbelTailMean
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : 0 < t := ht
    have hset : {ω | t < max (G ω) 0} = {ω | G ω ≤ t}ᶜ := by
      ext ω; simp only [ZeroCert.zc_mem_setOf_eq, mem_compl_iff, not_le, lt_max_iff]
      constructor
      · rintro (h | h); exact h; linarith
      · intro h; exact Or.inl h
    rw [hset, measureReal_compl (measurableSet_le hGm measurable_const), probReal_univ,
      prob_gumbelG_le μ hn hX]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : 0 < t := ht
    have hset : {ω | t < max (-G ω) 0} = {ω | G ω < -t} := by
      ext ω; simp only [ZeroCert.zc_mem_setOf_eq, lt_max_iff]
      constructor
      · rintro (h | h); linarith; linarith
      · intro h; exact Or.inl (by linarith)
    rw [hset, prob_gumbelG_lt μ hn hX]

/-- The uniform second-moment constant `C₂ = ∫_0^∞ 2 e^{-√t/2} dt`. -/
noncomputable def gumbelC2 : ℝ := ∫ t in Ioi (0 : ℝ), 2 * exp (-(√t / 2))

lemma integrableOn_exp_neg_sqrt : IntegrableOn (fun t : ℝ => 2 * exp (-(√t / 2))) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff _ (show (2 : ℝ) ≠ 0 by norm_num)]
  have h : IntegrableOn (fun x : ℝ => 4 * (x * exp (-(1 / 2) * x))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    exact IntegrableOn.congr_fun (this.const_mul 4) (fun x hx => by simp) measurableSet_Ioi
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Real.sqrt_sq hx.le,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

/-- **Lemma 5.1 (uniform second moment).** `E G_n² ≤ C₂` for all `n ≥ 2`. -/
theorem integral_gumbelG_sq_le {n : ℕ} (hn : 2 ≤ n) {X : ℕ → Ω → ℝ} (hX : IidStdGaussian μ n X) :
    ∫ ω, gumbelG X n ω ^ 2 ∂μ ≤ gumbelC2 := by
  set G := gumbelG X n
  have hGm := gumbelG_measurable μ hX
  rw [(gumbelG_sq_integrable μ hX).integral_eq_integral_meas_lt
    (ae_of_all _ (fun ω => sq_nonneg _))]
  have hbound : ∀ t ∈ Ioi (0 : ℝ), μ.real {ω | t < G ω ^ 2} ≤ 2 * exp (-(√t / 2)) := by
    intro t ht
    have ht : 0 < t := ht
    set s := √t
    have hs : 0 < s := Real.sqrt_pos.mpr ht
    have hsub : {ω | t < G ω ^ 2} ⊆ {ω | G ω ≤ s}ᶜ ∪ {ω | G ω < -s} := by
      intro ω hω
      simp only [ZeroCert.zc_mem_setOf_eq] at hω
      have : s < |G ω| := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt ht.le hω
      simp only [mem_union, mem_compl_iff, ZeroCert.zc_mem_setOf_eq, not_le]
      rcases le_total 0 (G ω) with h | h
      · left; rw [abs_of_nonneg h] at this; exact this
      · right; rw [abs_of_nonpos h] at this; linarith
    calc μ.real {ω | t < G ω ^ 2}
        ≤ μ.real ({ω | G ω ≤ s}ᶜ ∪ {ω | G ω < -s}) := measureReal_mono hsub
      _ ≤ μ.real {ω | G ω ≤ s}ᶜ + μ.real {ω | G ω < -s} := measureReal_union_le _ _
      _ = (1 - gumbelF n s) + gumbelF n (-s) := by
          rw [measureReal_compl (measurableSet_le hGm measurable_const), probReal_univ,
            prob_gumbelG_le μ hn hX, prob_gumbelG_lt μ hn hX]
      _ ≤ exp (-s) + exp (-(s / 2)) := by
          gcongr
          · exact gumbelF_right_tail hn hs.le
          · exact (gumbelF_left_tail hn hs.le).trans (exp_neg_exp_half_le s)
      _ ≤ 2 * exp (-(s / 2)) := by
          have : exp (-s) ≤ exp (-(s / 2)) := exp_le_exp.mpr (by linarith)
          linarith
  have hanti : Antitone (fun t => μ.real {ω | t < G ω ^ 2}) := by
    intro a b hab
    exact measureReal_mono (fun ω hω => lt_of_le_of_lt hab hω)
  have hint : IntegrableOn (fun t => μ.real {ω | t < G ω ^ 2}) (Ioi 0) := by
    refine integrableOn_exp_neg_sqrt.mono' hanti.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact hbound t ht
  exact setIntegral_mono_on hint integrableOn_exp_neg_sqrt measurableSet_Ioi hbound

end ZeroCert

end


-- =====================================================================
-- Part: Asymp6
-- =====================================================================

section

/-!
# Section 5: Lemma 5.1 (random-variable form), the conditional form of `I_n`, Taylor bound
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Lemma 5.1 (Gumbel limit with moment convergence).** For iid standard Gaussians,
`P{G_n ≤ x} → exp(-e^{-x})`, `E G_n → γ`, and `E G_n² ≤ C₂` for all `n ≥ 2`. -/
theorem gumbel_limit (X : ℕ → Ω → ℝ) (hX : ∀ m, IidStdGaussian μ m X) :
    (∀ x : ℝ, Tendsto (fun n => μ.real {ω | gumbelG X n ω ≤ x}) atTop
      (𝓝 (exp (-exp (-x))))) ∧
    Tendsto (fun n => ∫ ω, gumbelG X n ω ∂μ) atTop (𝓝 eulerMascheroniConstant) ∧
    (∀ n, 2 ≤ n → ∫ ω, gumbelG X n ω ^ 2 ∂μ ≤ gumbelC2) := by
  refine ⟨fun x => ?_, ?_, fun n hn => integral_gumbelG_sq_le μ hn (hX n)⟩
  · apply (gumbelF_tendsto x).congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (prob_gumbelG_le μ hn (hX n) x).symm
  · apply gumbelTailMean_tendsto.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (integral_gumbelG μ hn (hX n)).symm

/-- **Lemma 5.1 (consequence).** `M_n / b_n → 1` in probability. -/
theorem maxAbs_div_bn_tendsto (X : ℕ → Ω → ℝ) (hX : ∀ m, IidStdGaussian μ m X) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => μ.real {ω | ε ≤ |maxAbs X n ω / bn n - 1|}) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop, μ.real {ω | ε ≤ |maxAbs X n ω / bn n - 1|} ≤
      gumbelC2 / (ε ^ 2 * bn n ^ 4) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hb := bn_pos hn
    have hset : {ω | ε ≤ |maxAbs X n ω / bn n - 1|} =
        {ω | ε ^ 2 * bn n ^ 4 ≤ gumbelG X n ω ^ 2} := by
      ext ω
      simp only [ZeroCert.zc_mem_setOf_eq]
      have : maxAbs X n ω / bn n - 1 = gumbelG X n ω / bn n ^ 2 := by
        unfold gumbelG; field_simp
      rw [this, abs_div, abs_of_pos (by positivity : (0 : ℝ) < bn n ^ 2), le_div_iff₀ (by positivity),
        ← sq_le_sq₀ (by positivity) (abs_nonneg _), sq_abs]
      constructor <;> intro h <;> nlinarith
    rw [hset, le_div_iff₀ (by positivity), mul_comm]
    calc ε ^ 2 * bn n ^ 4 * μ.real {ω | ε ^ 2 * bn n ^ 4 ≤ gumbelG X n ω ^ 2}
        ≤ ∫ ω, gumbelG X n ω ^ 2 ∂μ :=
          mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun ω => sq_nonneg _))
            (gumbelG_sq_integrable μ (hX n)) _
      _ ≤ gumbelC2 := integral_gumbelG_sq_le μ hn (hX n)
  have hlim : Tendsto (fun n => gumbelC2 / (ε ^ 2 * bn n ^ 4)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply Tendsto.const_mul_atTop (by positivity)
    exact (tendsto_pow_atTop (by norm_num)).comp bn_tendsto_atTop
  exact squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hbound hlim

/-! ## `I_n(r) = E H̄(M_n / r)` -/

omit [MeasurableSpace Ω] in
lemma maxAbs_congr {Ω' : Type*} {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {n : ℕ} {ω : Ω} {ω' : Ω'} (h : ∀ k < n, X k ω = Y k ω') :
    maxAbs X n ω = maxAbs Y n ω' := by
  induction n with
  | zero => simp [maxAbs]
  | succ n ih =>
    simp only [maxAbs]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- **Equation (5.9).** `I_n(r) = E H̄(M_n/r)` for `r > 0`. -/
theorem ratioLaw_eq_integral_hnTail (n : ℕ) (X : ℕ → Ω → ℝ) (hX : IidStdGaussian μ (n + 1) X)
    {r : ℝ} (hr : 0 < r) :
    ratioLaw n r = ∫ ω, hnTail (maxAbs X n ω / r) ∂μ := by
  rw [← ratio_law μ n X hX r hr.le]
  -- the maximum as a function of the first `n` coordinates
  set φ : (Fin n → ℝ) → ℝ := fun v =>
    maxAbs (fun k (v : Fin n → ℝ) => if h : k < n then v ⟨k, h⟩ else 0) n v / r
  have hφm : Measurable φ := by
    apply Measurable.div_const
    apply maxAbs_measurable
    intro k hk
    simp only [hk, dite_true]
    exact measurable_pi_apply _
  have hφ : ∀ ω, φ (fun k => X k ω) = maxAbs X n ω / r := by
    intro ω
    simp only [φ]
    congr 1
    exact maxAbs_congr (fun k hk => by rw [ZeroCert.zc_dif_pos hk])
  obtain ⟨hlt, -⟩ := prob_lead_lt_eq_integral μ n X hX φ hφm
  simp_rw [hφ] at hlt
  have hae : {ω | ∀ k < n, |X k ω / X n ω| ≤ r} =ᵐ[μ] {ω | |X n ω| < maxAbs X n ω / r}ᶜ := by
    filter_upwards [hX.ae_ne_zero (k := n) (by omega)] with ω hω
    have hpos : 0 < |X n ω| := abs_pos.mpr hω
    apply propext
    show (∀ k < n, |X k ω / X n ω| ≤ r) ↔ ¬ (|X n ω| < maxAbs X n ω / r)
    rw [not_lt, div_le_iff₀ hr, mul_comm, maxAbs_le_iff X n ω (by positivity)]
    simp only [abs_div, div_le_iff₀ hpos]
  have hmeas : MeasurableSet {ω | |X n ω| < maxAbs X n ω / r} :=
    measurableSet_lt (hX.measurable (by omega)).abs
      ((maxAbs_measurable X n (fun k hk => hX.measurable (by omega))).div_const r)
  rw [measureReal_congr hae, measureReal_compl hmeas, probReal_univ, hlt]
  unfold hnTail
  rw [integral_sub (integrable_const _) (integrable_hnCDF_comp μ _
    ((maxAbs_measurable X n (fun k hk => hX.measurable (by omega))).div_const r))]
  simp

/-! ## Second-order Taylor bound for `H̄` -/

lemma mul_exp_neg_sq_le_one (t : ℝ) : |t| * exp (-t ^ 2 / 2) ≤ 1 := by
  have h1 : |t| ≤ exp (t ^ 2 / 2) := by
    have := add_one_le_exp (t ^ 2 / 2)
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have h2 : exp (-t ^ 2 / 2) * exp (t ^ 2 / 2) = 1 := by rw [← exp_add]; ring_nf; simp
  have h3 := exp_pos (-t ^ 2 / 2)
  nlinarith

/-- `h` is `h₀`-Lipschitz. -/
lemma hnDens_lipschitz (u v : ℝ) : |hnDens u - hnDens v| ≤ h0 * |u - v| := by
  have hd : ∀ x, HasDerivAt hnDens (-x * hnDens x) x := hnDens_hasDerivAt
  have hb : ∀ x, ‖-x * hnDens x‖ ≤ h0 := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (hnDens_pos x)]
    unfold hnDens
    have := mul_exp_neg_sq_le_one x
    have := h0_pos
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) convex_univ (mem_univ v) (mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- **Taylor bound.** For `x, y ≥ 0`,
`|H̄(y) - H̄(x) + h(x)(y - x)| ≤ (h₀/2)(y - x)²`. -/
theorem hnTail_taylor {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |hnTail y - hnTail x + hnDens x * (y - x)| ≤ h0 / 2 * (y - x) ^ 2 := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      |(∫ u in a..b, hnDens u) - hnDens a * (b - a)| ≤ h0 / 2 * (b - a) ^ 2 ∧
      |(∫ u in a..b, hnDens u) - hnDens b * (b - a)| ≤ h0 / 2 * (b - a) ^ 2 := by
    intro a b ha hab
    have hint := intervalIntegrable_hnDens a b
    constructor
    · have : (∫ u in a..b, hnDens u) - hnDens a * (b - a) = ∫ u in a..b, (hnDens u - hnDens a) := by
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const]; simp [mul_comm]
      rw [this]
      have hle := intervalIntegral.norm_integral_le_of_norm_le hab
        (f := fun u => hnDens u - hnDens a) (g := fun u => h0 * (u - a))
        (ae_of_all _ (fun u hu => by
          rw [Real.norm_eq_abs]
          have := hnDens_lipschitz u a
          rwa [abs_of_nonneg (by linarith [hu.1] : 0 ≤ u - a)] at this))
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _)
      rw [Real.norm_eq_abs] at hle
      refine hle.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x => x), integral_id]
      ring
    · have : (∫ u in a..b, hnDens u) - hnDens b * (b - a) = ∫ u in a..b, (hnDens u - hnDens b) := by
        rw [intervalIntegral.integral_sub hint intervalIntegrable_const]; simp [mul_comm]
      rw [this]
      have hle := intervalIntegral.norm_integral_le_of_norm_le hab
        (f := fun u => hnDens u - hnDens b) (g := fun u => h0 * (b - u))
        (ae_of_all _ (fun u hu => by
          rw [Real.norm_eq_abs]
          have := hnDens_lipschitz u b
          rwa [abs_sub_comm u b, abs_of_nonneg (by linarith [hu.2] : 0 ≤ b - u)] at this))
        (Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _)
      rw [Real.norm_eq_abs] at hle
      refine hle.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x => x), integral_id]
      ring
  unfold hnTail
  rcases le_total x y with hxy | hxy
  · have h1 := (key x y hx hxy).1
    rw [← hnCDF_sub hx hxy] at h1
    rw [show 1 - hnCDF y - (1 - hnCDF x) + hnDens x * (y - x) =
      -((hnCDF y - hnCDF x) - hnDens x * (y - x)) by ring, abs_neg]
    exact h1
  · have h1 := (key y x hy hxy).2
    rw [← hnCDF_sub hy hxy] at h1
    rw [show 1 - hnCDF y - (1 - hnCDF x) + hnDens x * (y - x) =
      (hnCDF x - hnCDF y) - hnDens x * (x - y) by ring]
    rw [show (y - x) ^ 2 = (x - y) ^ 2 by ring]
    exact h1

end ZeroCert

end


-- =====================================================================
-- Part: Asymp7
-- =====================================================================

section

/-!
# Section 5: Theorem 5.2, second-order inverse of the ratio certificate
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Equation (5.11): `I_n(r_n(c)) = p - a h(a)(γ - c)/b_n² + o(b_n^{-2})`, where
`r_n(c) = (b_n + c/b_n)/a_p`. -/
theorem ratioLaw_expansion (X : ℕ → Ω → ℝ) (hX : ∀ m, IidStdGaussian μ m X) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (c : ℝ) :
    Tendsto (fun n => bn n ^ 2 * (ratioLaw n ((bn n + c / bn n) / ap p) - p)) atTop
      (𝓝 (-(ap p * hnDens (ap p)) * (eulerMascheroniConstant - c))) := by
  set a := ap p with ha_def
  have ha : 0 < a := ap_pos hp0 hp1
  have hpa : hnTail a = p := hnTail_ap hp0 hp1
  -- eventually `b_n² + c > 0`
  have hb2 : Tendsto (fun n => bn n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp bn_tendsto_atTop
  have hev : ∀ᶠ n in atTop, 2 ≤ n ∧ 0 < bn n ^ 2 + c := by
    filter_upwards [eventually_ge_atTop 2, hb2.eventually (eventually_gt_atTop (-c))] with n h1 h2
    exact ⟨h1, by linarith⟩
  set G := fun n => gumbelG X n
  set E := fun n => ∫ ω, G n ω ∂μ
  set R : ℕ → Ω → ℝ := fun n ω =>
    hnTail (maxAbs X n ω / ((bn n + c / bn n) / a)) - hnTail a +
      hnDens a * (maxAbs X n ω / ((bn n + c / bn n) / a) - a)
  -- the decomposition
  have hdecomp : ∀ᶠ n in atTop, bn n ^ 2 * (ratioLaw n ((bn n + c / bn n) / a) - p) =
      -(a * hnDens a) * (E n - c) * (bn n ^ 2 / (bn n ^ 2 + c)) +
        bn n ^ 2 * ∫ ω, R n ω ∂μ := by
    filter_upwards [hev] with n ⟨hn, hbc⟩
    have hb := bn_pos hn
    set b := bn n
    have hr : 0 < (b + c / b) / a := by
      have : b + c / b = (b ^ 2 + c) / b := by field_simp
      rw [this]; positivity
    have hMm := maxAbs_measurable X n (fun k hk => (hX n).measurable hk)
    have hD : ∀ ω, maxAbs X n ω / ((b + c / b) / a) - a = a * (G n ω - c) / (b ^ 2 + c) := by
      intro ω
      simp only [G, gumbelG]
      have : b + c / b = (b ^ 2 + c) / b := by field_simp
      rw [this]; field_simp; ring
    have hInt : ratioLaw n ((b + c / b) / a) = ∫ ω, hnTail (maxAbs X n ω / ((b + c / b) / a)) ∂μ :=
      ratioLaw_eq_integral_hnTail μ n X (hX (n + 1)) hr
    have hTi : Integrable (fun ω => hnTail (maxAbs X n ω / ((b + c / b) / a))) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hnTail_continuous.measurable.comp (hMm.div_const _)).aestronglyMeasurable)
        (ae_of_all _ (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_of_pos (hnTail_pos _)]; exact hnTail_le_one _
    have hGi := gumbelG_integrable μ (hX n)
    have hDi : Integrable (fun ω => maxAbs X n ω / ((b + c / b) / a) - a) μ := by
      simp_rw [hD]
      exact ((hGi.sub (integrable_const c)).const_mul a).div_const _
    have hRi : Integrable (R n) μ :=
      (hTi.sub (integrable_const _)).add (hDi.const_mul _)
    have h1 : ratioLaw n ((b + c / b) / a) - p = ∫ ω, R n ω ∂μ -
        hnDens a * ∫ ω, (maxAbs X n ω / ((b + c / b) / a) - a) ∂μ := by
      rw [hInt, ← hpa, ← integral_const_mul, ← integral_sub hRi (hDi.const_mul _)]
      rw [show hnTail a = ∫ ω, hnTail a ∂μ by simp, ← integral_sub hTi (integrable_const _)]
      congr 1; funext ω; simp only [R]; ring
    have h2 : ∫ ω, (maxAbs X n ω / ((b + c / b) / a) - a) ∂μ = a * (E n - c) / (b ^ 2 + c) := by
      simp_rw [hD]
      rw [integral_div, integral_const_mul, integral_sub hGi (integrable_const c)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rfl
    rw [h1, h2]
    field_simp
    ring
  -- the remainder is `o(b_n^{-2})`
  have hRbound : ∀ᶠ n in atTop, |bn n ^ 2 * ∫ ω, R n ω ∂μ| ≤
      h0 / 2 * a ^ 2 * (2 * gumbelC2 + 2 * c ^ 2) * (bn n ^ 2 / (bn n ^ 2 + c) ^ 2) := by
    filter_upwards [hev] with n ⟨hn, hbc⟩
    have hb := bn_pos hn
    set b := bn n
    have hD : ∀ ω, maxAbs X n ω / ((b + c / b) / a) - a = a * (G n ω - c) / (b ^ 2 + c) := by
      intro ω
      simp only [G, gumbelG]
      have : b + c / b = (b ^ 2 + c) / b := by field_simp
      rw [this]; field_simp; ring
    have hr : 0 < (b + c / b) / a := by
      have : b + c / b = (b ^ 2 + c) / b := by field_simp
      rw [this]; positivity
    have hGi := gumbelG_integrable μ (hX n)
    have hG2i := gumbelG_sq_integrable μ (hX n)
    have hRle : ∀ ω, |R n ω| ≤ h0 / 2 * (a ^ 2 / (b ^ 2 + c) ^ 2) * (G n ω - c) ^ 2 := by
      intro ω
      have := hnTail_taylor ha.le (div_nonneg (maxAbs_nonneg X n ω) hr.le)
        (y := maxAbs X n ω / ((b + c / b) / a))
      simp only [R]
      refine this.trans (le_of_eq ?_)
      rw [hD]; field_simp
    have hsq : ∫ ω, (G n ω - c) ^ 2 ∂μ ≤ 2 * gumbelC2 + 2 * c ^ 2 := by
      have hi : Integrable (fun ω => 2 * G n ω ^ 2 + 2 * c ^ 2) μ :=
        (hG2i.const_mul 2).add (integrable_const _)
      calc ∫ ω, (G n ω - c) ^ 2 ∂μ ≤ ∫ ω, (2 * G n ω ^ 2 + 2 * c ^ 2) ∂μ := by
            apply integral_mono_of_nonneg (ae_of_all _ (fun ω => sq_nonneg _)) hi
            exact ae_of_all _ (fun ω => by nlinarith [sq_nonneg (G n ω + c)])
        _ = 2 * ∫ ω, G n ω ^ 2 ∂μ + 2 * c ^ 2 := by
            rw [integral_add (hG2i.const_mul 2) (integrable_const _), integral_const_mul]
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
            rfl
        _ ≤ 2 * gumbelC2 + 2 * c ^ 2 := by
            have := integral_gumbelG_sq_le μ hn (hX n)
            simp only [G] at *; linarith
    have hsqi : Integrable (fun ω => (G n ω - c) ^ 2) μ := by
      have : (fun ω => (G n ω - c) ^ 2) = fun ω => G n ω ^ 2 - 2 * c * G n ω + c ^ 2 := by
        funext ω; ring
      rw [this]
      exact (hG2i.sub (hGi.const_mul _)).add (integrable_const _)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < b ^ 2)]
    calc b ^ 2 * |∫ ω, R n ω ∂μ| ≤ b ^ 2 * ∫ ω, h0 / 2 * (a ^ 2 / (b ^ 2 + c) ^ 2) *
          (G n ω - c) ^ 2 ∂μ := by
          gcongr
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le (hsqi.const_mul _) (ae_of_all _ (fun ω => by
            rw [Real.norm_eq_abs]; exact hRle ω))
      _ = h0 / 2 * a ^ 2 * (∫ ω, (G n ω - c) ^ 2 ∂μ) * (b ^ 2 / (b ^ 2 + c) ^ 2) := by
          rw [integral_const_mul]; field_simp
      _ ≤ h0 / 2 * a ^ 2 * (2 * gumbelC2 + 2 * c ^ 2) * (b ^ 2 / (b ^ 2 + c) ^ 2) := by
          have := h0_pos
          gcongr
  -- limits of the auxiliary ratios
  have hq1 : Tendsto (fun n => bn n ^ 2 / (bn n ^ 2 + c)) atTop (𝓝 1) := by
    have : Tendsto (fun n => 1 / (1 + c * (bn n ^ 2)⁻¹)) atTop (𝓝 (1 / (1 + c * 0))) := by
      apply Tendsto.div tendsto_const_nhds _ (by simp)
      exact tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hb2))
    simp only [mul_zero, add_zero, div_one] at this
    apply this.congr'
    filter_upwards [hev] with n ⟨hn, _⟩
    have hb := bn_pos hn
    field_simp
  have hq2 : Tendsto (fun n => bn n ^ 2 / (bn n ^ 2 + c) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => bn n ^ 2 / (bn n ^ 2 + c) * (bn n ^ 2 + c)⁻¹) atTop (𝓝 (1 * 0)) :=
      hq1.mul (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ c hb2))
    rw [mul_zero] at this
    apply this.congr'
    filter_upwards [hev] with n ⟨hn, hbc⟩
    field_simp
  have hmain : Tendsto (fun n => -(a * hnDens a) * (E n - c) * (bn n ^ 2 / (bn n ^ 2 + c)))
      atTop (𝓝 (-(a * hnDens a) * (eulerMascheroniConstant - c) * 1)) := by
    apply Tendsto.mul _ hq1
    apply Tendsto.const_mul
    exact ((gumbel_limit μ X hX).2.1).sub_const c
  have hrem : Tendsto (fun n => bn n ^ 2 * ∫ ω, R n ω ∂μ) atTop (𝓝 0) := by
    have hlim := hq2.const_mul (h0 / 2 * a ^ 2 * (2 * gumbelC2 + 2 * c ^ 2))
    rw [mul_zero] at hlim
    exact squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hRbound) hlim
  rw [mul_one] at hmain
  have := hmain.add hrem
  rw [add_zero] at this
  exact this.congr' (by filter_upwards [hdecomp] with n hn; exact hn.symm)

end ZeroCert

end


-- =====================================================================
-- Part: Asymp8
-- =====================================================================

section

/-!
# Section 5: Theorem 5.2, equation (5.7)
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

/-- The canonical iid standard Gaussian sequence on `ℕ → ℝ`. -/
noncomputable def gaussSeq : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gaussSeq := by unfold gaussSeq; infer_instance

lemma gaussSeq_iid (m : ℕ) : IidStdGaussian gaussSeq m (fun k ω => ω k) where
  gauss k _ := ⟨measurable_pi_apply k, by
    unfold gaussSeq; exact Measure.infinitePi_map_eval _ k⟩
  indep := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => x)
      (fun _ => measurable_id)
    exact h.precomp (g := fun k : Fin m => (k : ℕ)) Fin.val_injective

lemma lt_ratioLawInv {n : ℕ} (hn : 1 ≤ n) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r)
    (h : ratioLaw n r < p) : r < ratioLawInv n p := by
  obtain ⟨-, -, -, hsm, hq⟩ := ratioLaw_properties n hn
  obtain ⟨hq0, hqp, -⟩ := hq p hp0 hp1
  by_contra hle; push Not at hle
  have := hsm.monotoneOn hq0 hr hle
  linarith

lemma ratioLawInv_le {n : ℕ} (hn : 1 ≤ n) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r)
    (h : p < ratioLaw n r) : ratioLawInv n p ≤ r := by
  obtain ⟨-, -, -, hsm, hq⟩ := ratioLaw_properties n hn
  obtain ⟨hq0, hqp, -⟩ := hq p hp0 hp1
  by_contra hlt; push Not at hlt
  have := hsm.monotoneOn hr hq0 hlt.le
  linarith

/-- **Theorem 5.2, equation (5.7).** For fixed `0 < p < 1`,
`I_n^{-1}(p) = (b_n + γ/b_n + o(1/b_n)) / a_p`, i.e. `b_n (a_p I_n^{-1}(p) - b_n) → γ`. -/
theorem ratioLawInv_second_order {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => bn n * (ap p * ratioLawInv n p - bn n)) atTop
      (𝓝 eulerMascheroniConstant) := by
  set a := ap p
  have ha : 0 < a := ap_pos hp0 hp1
  have hha : 0 < a * hnDens a := mul_pos ha (hnDens_pos a)
  have hX := gaussSeq_iid
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set c := (a' + eulerMascheroniConstant) / 2
    have hc1 : a' < c := by simp only [c]; linarith
    have hc2 : c < eulerMascheroniConstant := by simp only [c]; linarith
    have hlim := ratioLaw_expansion gaussSeq (fun k ω => ω k) hX hp0 hp1 c
    have hneg : -(a * hnDens a) * (eulerMascheroniConstant - c) < 0 := by
      have : 0 < eulerMascheroniConstant - c := by linarith
      nlinarith
    filter_upwards [hlim.eventually (gt_mem_nhds hneg), eventually_ge_atTop 2,
      (bn_tendsto_atTop.eventually (eventually_gt_atTop (|c| + 1)))] with n h1 hn hbig
    have hb := bn_pos hn
    have hr : 0 ≤ (bn n + c / bn n) / a := by
      apply div_nonneg _ ha.le
      have : |c / bn n| ≤ bn n := by
        rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]; nlinarith [abs_nonneg c]
      linarith [neg_abs_le (c / bn n)]
    have hlt : ratioLaw n ((bn n + c / bn n) / a) < p := by
      have h2 : 0 < bn n ^ 2 := by positivity
      by_contra hge; push Not at hge
      have : 0 ≤ bn n ^ 2 * (ratioLaw n ((bn n + c / bn n) / a) - p) :=
        mul_nonneg h2.le (by linarith)
      linarith
    have := lt_ratioLawInv (by omega) hp0 hp1 hr hlt
    rw [div_lt_iff₀ ha] at this
    have h3 : c < bn n * (a * ratioLawInv n p - bn n) := by
      have : c / bn n < a * ratioLawInv n p - bn n := by linarith [mul_comm (ratioLawInv n p) a]
      rw [div_lt_iff₀ hb] at this; linarith
    linarith
  · intro a' ha'
    set c := (a' + eulerMascheroniConstant) / 2
    have hc1 : c < a' := by simp only [c]; linarith
    have hc2 : eulerMascheroniConstant < c := by simp only [c]; linarith
    have hlim := ratioLaw_expansion gaussSeq (fun k ω => ω k) hX hp0 hp1 c
    have hpos : 0 < -(a * hnDens a) * (eulerMascheroniConstant - c) := by
      have : eulerMascheroniConstant - c < 0 := by linarith
      nlinarith
    filter_upwards [hlim.eventually (lt_mem_nhds hpos), eventually_ge_atTop 2,
      (bn_tendsto_atTop.eventually (eventually_gt_atTop (|c| + 1)))] with n h1 hn hbig
    have hb := bn_pos hn
    have hr : 0 ≤ (bn n + c / bn n) / a := by
      apply div_nonneg _ ha.le
      have : |c / bn n| ≤ bn n := by
        rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]; nlinarith [abs_nonneg c]
      linarith [neg_abs_le (c / bn n)]
    have hgt : p < ratioLaw n ((bn n + c / bn n) / a) := by
      have h2 : 0 < bn n ^ 2 := by positivity
      by_contra hle; push Not at hle
      have : bn n ^ 2 * (ratioLaw n ((bn n + c / bn n) / a) - p) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h2.le (by linarith)
      linarith
    have := ratioLawInv_le (by omega) hp0 hp1 hr hgt
    rw [le_div_iff₀ ha] at this
    have h3 : bn n * (a * ratioLawInv n p - bn n) ≤ c := by
      have : a * ratioLawInv n p - bn n ≤ c / bn n := by linarith [mul_comm (ratioLawInv n p) a]
      rw [le_div_iff₀ hb] at this; linarith
    linarith

end ZeroCert

end


-- =====================================================================
-- Part: Asymp9
-- =====================================================================

section

/-!
# Section 5: Theorem 5.2, the expansion in terms of `log n` (equation (5.8))
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

lemma log_h0 : log h0 = (log 2 - log π) / 2 := by
  unfold h0
  rw [Real.log_sqrt (by positivity), Real.log_div (by norm_num) (by positivity)]

/-- The Mills remainder `θ_n = log n - (b_n²/2 + log b_n - log h₀) ∈ [0, log(1 + b_n^{-2})]`. -/
lemma mills_log_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ log n - (bn n ^ 2 / 2 + log (bn n) - log h0) ∧
    log n - (bn n ^ 2 / 2 + log (bn n) - log h0) ≤ log (1 + (bn n ^ 2)⁻¹) := by
  have hb := bn_pos hn
  set b := bn n
  have hn' : (0 : ℝ) < n := by positivity
  have htail := hnTail_bn hn
  have hlogD : log (hnDens b) = log h0 + -b ^ 2 / 2 := by
    unfold hnDens; rw [log_mul h0_pos.ne' (exp_pos _).ne', log_exp]
  constructor
  · have h := mills_upper hb
    rw [htail] at h
    have := Real.log_le_log (by positivity) h
    rw [log_div (hnDens_pos b).ne' hb.ne', hlogD, one_div, log_inv] at this
    linarith
  · have h := mills_lower hb
    rw [htail] at h
    have := Real.log_le_log (by have := hnDens_pos b; positivity) h
    rw [log_mul (by positivity) (hnDens_pos b).ne', log_div hb.ne' (by positivity), hlogD,
      one_div, log_inv] at this
    have h1 : log (1 + (b ^ 2)⁻¹) = log (1 + b ^ 2) - 2 * log b := by
      rw [show 1 + (b ^ 2)⁻¹ = (1 + b ^ 2) / b ^ 2 by field_simp; ring, log_div (by positivity)
        (by positivity), log_pow]
      push_cast; ring
    rw [h1]
    linarith

lemma log_div_sq_tendsto : Tendsto (fun n => log (bn n) / bn n ^ 2) atTop (𝓝 0) := by
  have h := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := (h.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp bn_tendsto_atTop)).const_mul
    (1 / 2)
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hb := bn_pos hn
  simp only [Function.comp, pow_one, one_mul, add_zero, log_pow]
  push_cast; field_simp

/-- The Mills remainder `θ_n`. -/
noncomputable def millsTheta (n : ℕ) : ℝ := log n - (bn n ^ 2 / 2 + log (bn n) - log h0)

lemma millsTheta_tendsto : Tendsto millsTheta atTop (𝓝 0) := by
  have hup : Tendsto (fun n => log (1 + (bn n ^ 2)⁻¹)) atTop (𝓝 0) := by
    have : Tendsto (fun n => 1 + (bn n ^ 2)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by norm_num)).comp bn_tendsto_atTop))
    rw [add_zero] at this
    have := (continuousAt_log one_ne_zero).tendsto.comp this
    simpa [Function.comp_def] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (by filter_upwards [eventually_ge_atTop 2] with n hn using (mills_log_bounds hn).1)
    (by filter_upwards [eventually_ge_atTop 2] with n hn using (mills_log_bounds hn).2)

/-- `2 log n / b_n² → 1`. -/
lemma two_log_div_bn_sq_tendsto : Tendsto (fun n : ℕ => 2 * log n / bn n ^ 2) atTop (𝓝 1) := by
  have hθ := millsTheta_tendsto
  have h1 : Tendsto (fun n => 1 + 2 * (log (bn n) / bn n ^ 2) +
      (log π - log 2) * (bn n ^ 2)⁻¹ + 2 * millsTheta n * (bn n ^ 2)⁻¹) atTop
      (𝓝 (1 + 2 * 0 + (log π - log 2) * 0 + 2 * 0 * 0)) := by
    have hinv : Tendsto (fun n => (bn n ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp bn_tendsto_atTop)
    exact ((tendsto_const_nhds.add (log_div_sq_tendsto.const_mul 2)).add
      (hinv.const_mul _)).add ((hθ.const_mul 2).mul hinv)
  simp only [mul_zero, add_zero] at h1
  apply h1.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hb := bn_pos hn
  simp only [millsTheta]
  rw [log_h0]
  field_simp
  ring

/-- `b_n² = 2 log n - log log n - log π + o(1)`. -/
theorem bn_sq_expansion :
    Tendsto (fun n : ℕ => bn n ^ 2 - (2 * log n - log (log n) - log π)) atTop (𝓝 0) := by
  have hθ := millsTheta_tendsto
  have hratio := two_log_div_bn_sq_tendsto
  have hlog : Tendsto (fun n : ℕ => log (2 * log n / bn n ^ 2)) atTop (𝓝 0) := by
    have := (continuousAt_log one_ne_zero).tendsto.comp hratio
    simpa [Function.comp_def] using this
  have := hlog.sub (hθ.const_mul 2)
  rw [mul_zero, sub_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hb := bn_pos (by omega : 2 ≤ n)
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < log (n : ℝ) := log_pos hn'
  show log (2 * log n / bn n ^ 2) - 2 * (log n - (bn n ^ 2 / 2 + log (bn n) - log h0)) = _

  rw [log_div (by positivity) (by positivity), log_mul (by norm_num) hL.ne', log_pow, log_h0]
  push_cast
  ring

end ZeroCert

end


-- =====================================================================
-- Part: Asymp10
-- =====================================================================

section

/-!
# Section 5: Theorem 5.2, equation (5.8)
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

lemma log_nat_tendsto : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `(log L + c)² / L → 0` as `L = log n → ∞`. -/
lemma log_log_sq_div_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ => (log (log n) + c) ^ 2 / log n) atTop (𝓝 0) := by
  have h2 := (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp log_nat_tendsto
  have h1 := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp log_nat_tendsto
  have h0 : Tendsto (fun n : ℕ => (log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp log_nat_tendsto
  have := (h2.add (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))
  simp only [mul_zero, add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < log (n : ℝ) := log_pos hn'
  simp only [Function.comp, one_mul, pow_one]
  field_simp
  ring

/-- `b_n = √(2L) - (log L + log π)/(2√(2L)) + o(L^{-1/2})`, `L = log n`. -/
theorem bn_expansion :
    Tendsto (fun n : ℕ => √(2 * log n) * (bn n - √(2 * log n)) +
      (log (log n) + log π) / 2) atTop (𝓝 0) := by
  set L : ℕ → ℝ := fun n => log n
  set D : ℕ → ℝ := fun n => bn n ^ 2 - 2 * L n
  have hE := bn_sq_expansion
  -- `D² / (2 (b + s)²) → 0`
  have hsq : Tendsto (fun n => D n ^ 2 / (2 * (bn n + √(2 * L n)) ^ 2)) atTop (𝓝 0) := by
    have hE2 : Tendsto (fun n : ℕ => (bn n ^ 2 - (2 * log n - log (log n) - log π)) ^ 2 / log n)
        atTop (𝓝 0) := by
      have := (hE.pow 2).mul (tendsto_inv_atTop_zero.comp log_nat_tendsto)
      simpa [div_eq_mul_inv] using this
    have hbound := (hE2.add (log_log_sq_div_tendsto (log π))).div_const 2
    rw [zero_add, zero_div] at hbound
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_ge_atTop 3] with n hn
      positivity
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have hb := bn_pos (by omega : 2 ≤ n)
      have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hL : 0 < log (n : ℝ) := log_pos hn'
      have hs : 0 < √(2 * L n) := Real.sqrt_pos.mpr (by simp only [L]; positivity)
      have hs2 : √(2 * L n) ^ 2 = 2 * L n := Real.sq_sqrt (by simp only [L]; positivity)
      have hden : 4 * L n ≤ 2 * (bn n + √(2 * L n)) ^ 2 := by nlinarith
      set u := bn n ^ 2 - (2 * log n - log (log n) - log π)
      set v := log (log (n : ℝ)) + log π
      have hDuv : D n = u - v := by simp only [D, u, v, L]; ring
      have hD2 : D n ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by rw [hDuv]; nlinarith [sq_nonneg (u + v)]
      calc D n ^ 2 / (2 * (bn n + √(2 * L n)) ^ 2) ≤ (2 * u ^ 2 + 2 * v ^ 2) / (4 * L n) := by
            apply div_le_div₀ (by positivity) hD2 (by simp only [L]; positivity) hden
        _ = (u ^ 2 / log n + v ^ 2 / log n) / 2 := by simp only [L]; field_simp; ring
  have := hE.div_const 2 |>.sub hsq
  rw [zero_div, sub_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hb := bn_pos (by omega : 2 ≤ n)
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < log (n : ℝ) := log_pos hn'
  have hs : 0 < √(2 * log n) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(2 * log n) ^ 2 = 2 * log n := Real.sq_sqrt (by positivity)
  simp only [D, L]
  set s := √(2 * log (n : ℝ))
  have hbs : 0 < bn n + s := by positivity
  field_simp
  rw [← hs2]
  ring

/-- **Theorem 5.2, equation (5.8).** For fixed `0 < p < 1`, with `L = log n`,
`a_p I_n^{-1}(p) = √(2L) - (log L + log π - 2γ)/(2√(2L)) + o(L^{-1/2})`. -/
theorem ratioLawInv_log_expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => √(2 * log n) * (ap p * ratioLawInv n p - √(2 * log n)) +
      (log (log n) + log π - 2 * eulerMascheroniConstant) / 2) atTop (𝓝 0) := by
  have h57 := ratioLawInv_second_order hp0 hp1
  have hB := bn_expansion
  -- `√(2L)/b_n → 1`
  have hsb : Tendsto (fun n : ℕ => √(2 * log n) / bn n) atTop (𝓝 1) := by
    have := (continuous_sqrt.tendsto 1).comp two_log_div_bn_sq_tendsto
    rw [Real.sqrt_one] at this
    apply this.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hb := bn_pos hn
    simp only [Function.comp]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hb.le]
  have := hB.add ((hsb.mul h57).sub_const eulerMascheroniConstant)
  rw [one_mul, sub_self, add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hb := bn_pos hn
  field_simp
  ring

end ZeroCert

end


-- =====================================================================
-- Part: Indep
-- =====================================================================

section

/-!
# Section 5: Corollary 5.3 (comparison with independent Cauchy maxima)
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Set

namespace ZeroCert

/-- The `p`-quantile of the maximum modulus of `n` independent standard Cauchy variables,
`q^{ind}_{n,p} = tan(π p^{1/n} / 2)`. -/
noncomputable def indepCauchyQuantile (n : ℕ) (p : ℝ) : ℝ := tan (π / 2 * p ^ (1 / (n : ℝ)))

/-- The half-normal probability measure `h(x) dx` on `(0, ∞)`. -/
noncomputable def halfNormalMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (hnDens x))

lemma integral_halfNormalMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂halfNormalMeasure = ∫ x in Ioi 0, hnDens x * f x := by
  have hm : Measurable (fun x => (hnDens x).toNNReal) :=
    hnDens_continuous.measurable.real_toNNReal
  have := integral_withDensity_eq_integral_smul hm (μ := volume.restrict (Ioi 0)) f
  unfold halfNormalMeasure
  simp only [ENNReal.ofReal] at *
  rw [this]
  refine integral_congr_ae (ae_of_all _ (fun x => ?_))
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hnDens_pos x).le]

instance : IsProbabilityMeasure halfNormalMeasure := by
  constructor
  unfold halfNormalMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_hnDens, ENNReal.ofReal_one]
  · exact integrable_hnDens.integrableOn
  · exact ae_of_all _ (fun x => (hnDens_pos x).le)

/-- **Corollary 5.3, equation (5.10)**: the independent-Cauchy law is a valid lower bound,
`I_n(r) ≥ ((2/π) arctan r)^n` (by Jensen's inequality). -/
theorem ratioLaw_ge_indep (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (2 / π * arctan r) ^ n ≤ ratioLaw n r := by
  rw [← ratioLaw_one hr, ratioLaw_eq_ratioJ 1 hr, ratioLaw_eq_ratioJ n hr]
  unfold ratioJ
  simp only [pow_one]
  rw [← integral_halfNormalMeasure, ← integral_halfNormalMeasure]
  have hfc : Continuous fun x => hnCDF (r * x) :=
    hnCDF_continuous.comp (continuous_const.mul continuous_id)
  have hbdd : ∀ x, ‖hnCDF (r * x)‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnCDF_nonneg _)]; exact hnCDF_le_one _
  have hint : Integrable (fun x => hnCDF (r * x)) halfNormalMeasure :=
    Integrable.of_bound hfc.aestronglyMeasurable 1 (ae_of_all _ hbdd)
  have hint2 : Integrable (fun x => hnCDF (r * x) ^ n) halfNormalMeasure :=
    Integrable.of_bound (hfc.pow n).aestronglyMeasurable 1 (ae_of_all _ (fun x => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hbdd x)))
  exact (convexOn_pow n).map_integral_le (continuous_pow n).continuousOn isClosed_Ici
    (ae_of_all _ (fun x => hnCDF_nonneg _)) hint hint2

/-- **Corollary 5.3, exact independent quantile**: for `n ≥ 1` and `0 < p < 1`, the distribution
function `((2/π) arctan r)^n` of the maximum modulus of `n` independent standard Cauchy variables
equals `p` at `r = q^{ind}_{n,p}`. -/
theorem indepCauchyQuantile_spec {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < indepCauchyQuantile n p ∧ (2 / π * arctan (indepCauchyQuantile n p)) ^ n = p := by
  have hn0 : n ≠ 0 := by omega
  set u := p ^ (1 / (n : ℝ)) with hu
  have hu0 : 0 < u := rpow_pos_of_pos hp0 _
  have hu1 : u < 1 := rpow_lt_one hp0.le hp1 (by positivity)
  have hx0 : 0 < π / 2 * u := by positivity
  have hx1 : π / 2 * u < π / 2 := by nlinarith [pi_pos]
  refine ⟨tan_pos_of_pos_of_lt_pi_div_two hx0 hx1, ?_⟩
  unfold indepCauchyQuantile
  rw [← hu, arctan_tan (by linarith [pi_pos]) hx1]
  have : 2 / π * (π / 2 * u) = u := by field_simp
  rw [this, hu, one_div, rpow_inv_natCast_pow hp0.le hn0]

/-- **Corollary 5.3, equation (5.9)**: `q^{ind}_{n,p} ∼ 2n / (π log(1/p))`. -/
theorem indepCauchyQuantile_asymp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => indepCauchyQuantile n p / (2 * n / (π * log (1 / p)))) atTop
      (𝓝 1) := by
  set L := log (1 / p) with hL
  have hL0 : 0 < L := log_pos (by rw [lt_div_iff₀ hp0]; linarith)
  -- the function-level limit as `ε → 0⁺`
  have hfun : Tendsto (fun ε : ℝ => tan (π / 2 * exp (-ε)) * (π * ε / 2)) (𝓝[>] 0)
      (𝓝 1) := by
    set v : ℝ → ℝ := fun ε => π / 2 * (1 - exp (-ε)) with hv
    have hd1 : HasDerivAt (fun t : ℝ => 1 - exp (-t)) 1 0 := by
      have := ((hasDerivAt_neg (0 : ℝ)).exp).const_sub 1
      simpa using this
    have hs1 := hd1.tendsto_slope_zero_right
    simp only [zero_add, neg_zero, exp_zero, sub_self, sub_zero, smul_eq_mul] at hs1
    -- `v ε → 0` within `(0, ∞)`
    have hv0 : Tendsto v (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto v (𝓝 0) (𝓝 (π / 2 * (1 - exp (-0)))) :=
          (continuous_const.mul (continuous_const.sub (continuous_exp.comp continuous_neg))).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have : exp (-ε) < 1 := by exact exp_lt_one_iff.mpr (by simp at hε ⊢; linarith)
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hv]
        have := pi_pos; nlinarith
    have hsin := (hasDerivAt_sin 0).tendsto_slope_zero
    simp only [zero_add, sin_zero, sub_zero, smul_eq_mul, cos_zero] at hsin
    have hsin' : Tendsto (fun ε => (v ε)⁻¹ * sin (v ε)) (𝓝[>] 0) (𝓝 1) := hsin.comp hv0
    have hcos : Tendsto (fun ε => cos (v ε)) (𝓝[>] 0) (𝓝 1) := by
      have := (continuous_cos.tendsto 0).comp (hv0.mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def] using this
    have hlim := (hcos.mul (hs1.inv₀ one_ne_zero)).mul (hsin'.inv₀ one_ne_zero)
    simp only [inv_one, mul_one] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have he : exp (-ε) < 1 := exp_lt_one_iff.mpr (by linarith)
    have hvpos : 0 < v ε := by simp only [hv]; have := pi_pos; nlinarith
    have hvlt : v ε < π / 2 := by
      simp only [hv]; have := pi_pos; have := exp_pos (-ε); nlinarith
    have hsinpos : 0 < sin (v ε) := sin_pos_of_pos_of_lt_pi hvpos (by linarith)
    have htan : tan (π / 2 * exp (-ε)) = cos (v ε) / sin (v ε) := by
      have : π / 2 * exp (-ε) = π / 2 - v ε := by simp only [hv]; ring
      rw [this, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
    rw [htan]
    have h1e : 0 < 1 - exp (-ε) := by linarith
    simp only [hv] at hsinpos ⊢
    field_simp
  -- the sequence `ε_n = L / n → 0⁺`
  have hseq : Tendsto (fun n : ℕ => L / n) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_const_div_atTop_nhds_zero_nat L
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact div_pos hL0 this
  apply (hfun.comp hseq).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, indepCauchyQuantile]
  have hpow : p ^ (1 / (n : ℝ)) = exp (-(L / n)) := by
    rw [rpow_def_of_pos hp0, hL, one_div, one_div, log_inv]; ring_nf
  rw [hpow]
  field_simp


/-- **Corollary 5.3, first assertion**: the common-denominator ratio quantile is of order
`√(log n)`; precisely `a_p I_n^{-1}(p) / √(2 log n) → 1`. -/
theorem ratioLawInv_order {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => ap p * ratioLawInv n p / √(2 * log n)) atTop (𝓝 1) := by
  have h := ratioLawInv_log_expansion hp0 hp1
  set c := log π - 2 * eulerMascheroniConstant
  have hL : Tendsto (fun n : ℕ => 2 * log (n : ℝ)) atTop atTop :=
    log_nat_tendsto.const_mul_atTop (by norm_num)
  have hinv : Tendsto (fun n : ℕ => (2 * log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hll : Tendsto (fun n : ℕ => (log (log (n : ℝ)) + c) / 2 / (2 * log n)) atTop (𝓝 0) := by
    have h2 := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp log_nat_tendsto
    have := (h2.const_mul (1 / 4)).add (hinv.const_mul (c / 2))
    simp only [mul_zero, add_zero] at this
    apply this.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hL0 : 0 < log (n : ℝ) := log_pos hn'
    simp only [Function.comp, pow_one, one_mul]
    field_simp
    ring
  have hsum := (h.mul hinv).sub hll
  simp only [mul_zero, sub_zero] at hsum
  have := hsum.const_add 1
  simp only [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL0 : 0 < 2 * log (n : ℝ) := by have := log_pos hn'; linarith
  have hs : 0 < √(2 * log (n : ℝ)) := sqrt_pos.mpr hL0
  have hsq : √(2 * log (n : ℝ)) ^ 2 = 2 * log n := sq_sqrt hL0.le
  simp only [c]
  set s := √(2 * log (n : ℝ))
  rw [← hsq]
  field_simp
  ring

end ZeroCert

end
