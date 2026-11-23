module

public import LpGowers.DiscreteProofs
public import LpGowers.LebesgueProofs
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Counting-measure functionals and their critical exponents

This module connects the counting formula (1.11) to the Haar-measure definition
of the functional in (1.10), as required by Proposition 8.1.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Pointwise Topology

namespace LpGowers.Discrete

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- All binary vertices of the translated cube belong to A. -/
def fits {d : ℕ} (A : Finset G) (h : Fin d → G) (x : G) : Prop :=
  ∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ A

instance {d : ℕ} (A : Finset G) (h : Fin d → G) (x : G) : Decidable (fits A h x) :=
  inferInstanceAs (Decidable (∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ A))

omit [DecidableEq G] in
theorem fits_cons {d : ℕ} (A : Finset G) (a : G) (h : Fin d → G) (x : G) :
    fits A (Fin.cons a h) x ↔ fits A h x ∧ fits A h (x + a) := by
  classical
  constructor
  · intro hc
    constructor
    · intro s
      have := hc (s.map (Fin.succEmb d))
      simpa [Finset.sum_map] using this
    · intro s
      have := hc (insert 0 (s.map (Fin.succEmb d)))
      simpa [Finset.sum_map, Finset.sum_insert, add_assoc] using this
  · rintro ⟨h₀, h₁⟩ s
    let t := Finset.univ.filter (fun i : Fin d => i.succ ∈ s)
    have hs : ∑ i ∈ s, Fin.cons a h i =
        (if 0 ∈ s then a else 0) + ∑ i ∈ t, h i := by
      calc
        _ = ∑ i : Fin (d + 1), if i ∈ s then Fin.cons a h i else 0 := by simp
        _ = _ := by rw [Fin.sum_univ_succ]; simp [t, Finset.sum_filter]
    by_cases e : 0 ∈ s
    · simpa [hs, e, add_assoc] using h₁ t
    · simpa [hs, e] using h₀ t

/-- The indicator as a finite nonnegative function, in the common domain of the five theorems. -/
def finIndicator (A : Finset G) (x : G) : ℝ≥0 := if x ∈ A then 1 else 0

theorem cubeProduct_finIndicator (A : Finset G) (d : ℕ) (h : Fin d → G) (x : G) :
    cubeProduct d (finIndicator A) h x = if fits A h x then 1 else 0 := by
  induction d generalizing x with
  | zero =>
    have hf : fits A h x ↔ x ∈ A := by
      constructor
      · intro hv; simpa using hv ∅
      · intro hx s; have : s = ∅ := Subsingleton.elim _ _; simpa [this] using hx
    simp only [hf, cubeProduct, finIndicator]
    split <;> simp
  | succ d ih =>
    rw [← Fin.cons_self_tail h]
    simp only [fits_cons, cubeProduct, Fin.tail_cons, Fin.cons_zero, ih]
    split_ifs <;> simp_all

variable [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]

omit [AddCommGroup G] [DecidableEq G] in
theorem cubeMeasure_count (d : ℕ) :
    cubeMeasure (Measure.count : Measure G) d = Measure.count := by
  apply Measure.ext_of_singleton
  intro h
  simp [cubeMeasure]

omit [Countable G] in
theorem autocorrelation_finIndicator (A : Finset G) (d : ℕ) (h : Fin d → G) :
    autocorrelation Measure.count d (finIndicator A) h = (baseCount A h : ℝ≥0∞) := by
  unfold autocorrelation
  let B := A.filter (fits A h)
  have hI : (fun x => cubeProduct d (finIndicator A) h x) = (B : Set G).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hv : fits A h x
    · have hx : x ∈ A := by simpa using hv ∅
      simp [cubeProduct_finIndicator, B, hv, hx]
    · simp [cubeProduct_finIndicator, B, hv]
  rw [hI, lintegral_indicator_const B.measurableSet, one_mul, Measure.count_apply_finset]
  rfl

/-- Exact identity between the extended-real functional on an indicator and the finite
shared-increment count. The normalization is 1/(2^d p), with p=k+1>0. -/
theorem gowers_finIndicator (d k : ℕ) (A : Finset G) :
    gowers Measure.count d (k + 1 : ℕ) (finIndicator A) =
      (energy d (k + 1) A : ℝ≥0∞) ^ (1 / ((2 : ℝ) ^ d * (k + 1 : ℕ))) := by
  classical
  let H := Fintype.piFinset (fun _ : Fin d => A - A)
  have he : ∫⁻ h : Fin d → G, ((baseCount A h : ℝ≥0∞) ^ (k + 1 : ℕ)) ∂Measure.count =
      (energy d (k + 1) A : ℝ≥0∞) := by
    rw [lintegral_count, tsum_eq_sum (s := H)]
    · simp [energy, H]
    · intro h hn
      simp [baseCount_eq_zero_outside A h hn]
  simp only [gowers, lp, cubeMeasure_count, autocorrelation_finIndicator, ENNReal.rpow_natCast, he,
    ← ENNReal.rpow_mul]
  congr 1
  simp [one_div, mul_inv_rev]

omit [AddCommGroup G] [Countable G] in
theorem lp_finIndicator (A : Finset G) {q : ℝ} (hq : 0 < q) :
    lp Measure.count q (liftNN (finIndicator A)) = (A.card : ℝ≥0∞) ^ (1 / q) := by
  unfold lp
  have hI : (fun x => liftNN (finIndicator A) x ^ q) = (A : Set G).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, liftNN, finIndicator, hq]
  rw [hI, lintegral_indicator_const A.measurableSet, one_mul, Measure.count_apply_finset]

/-- Testing the functional inequality on indicators, as in Proposition 8.1(b) ⇒ (c). -/
theorem setExponent_of_functionExponent (d k n : ℕ) {q : ℝ} (hq : q ∈ functionExponents d (k + 1) n) :
    (2 : ℝ) ^ d * (k + 1 : ℕ) / q ∈ setExponents d (k + 1) n := by
  have hpos := hq.1
  refine ⟨by positivity, ?_⟩
  intro m A hA
  have htest := hq.2 m (finIndicator A) (fun x hx => ite_eq_right (fun ha => hx (hA ha)))
  rw [gowers_finIndicator, lp_finIndicator A hpos] at htest
  let M : ℝ := 2 ^ d * (k + 1 : ℕ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hp := ENNReal.rpow_le_rpow htest hM.le
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hp
  change (↑(energy d (k+1) A) : ℝ≥0∞) ^ ((1 / M) * M) ≤ (A.card : ℝ≥0∞) ^ ((1/q)*M) at hp
  rw [one_div_mul_cancel hM.ne', ENNReal.rpow_one, show 1/q*M = M/q by ring] at hp
  have hr := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (div_nonneg hM.le hpos.le) (by simp)) hp
  simpa [← ENNReal.toReal_rpow, M] using hr

/-- Probability-free estimate for powers under simultaneous pointwise and integral bounds. -/
private theorem lintegral_pow_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (hF : Measurable F) (M : ℝ≥0∞) (hpoint : ∀ x, F x ≤ M)
    (hint : ∫⁻ x, F x ∂μ ≤ M) (p : ℕ) (hp : 0 < p) : ∫⁻ x, F x ^ p ∂μ ≤ M ^ p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  calc
    _ ≤ ∫⁻ x, M ^ k * F x ∂μ := lintegral_mono fun x => by rw [pow_succ]; gcongr; exact hpoint x
    _ = M ^ k * ∫⁻ x, F x ∂μ := lintegral_const_mul _ hF
    _ ≤ _ := by rw [pow_succ]; gcongr

/-- On a lattice, the unnormalized mass of f controls every counted autocorrelation,
and its total mass, at the correct homogeneity. No restriction on cube size is used. -/
theorem lattice_autocorrelation_bounds (m : ℕ) (f : Lattice m → ℝ≥0) (d : ℕ) :
    let M := ∫⁻ x, (f x : ℝ≥0∞) ∂Measure.count
    (∀ h, autocorrelation Measure.count d f h ≤ M ^ (2 ^ d : ℕ)) ∧
    (∫⁻ h, autocorrelation Measure.count d f h ∂cubeMeasure Measure.count d) ≤ M ^ (2 ^ d : ℕ) := by
  let μ : Measure (Lattice m) := Measure.count
  let M : ℝ≥0∞ := ∫⁻ x, (f x : ℝ≥0∞) ∂μ
  have hf : Measurable f := .of_discrete
  have hbound (j : ℕ) (h : Fin j → Lattice m) : autocorrelation μ j f h ≤ M ^ (2 ^ j : ℕ) := by
    apply (autocorrelation_le_lintegral_pow μ j hf.aemeasurable h).trans
    apply lintegral_pow_le μ _ (.of_discrete) M _ le_rfl _ (by positivity)
    intro x
    show (f x : ℝ≥0∞) ≤ ∫⁻ x, (f x : ℝ≥0∞) ∂Measure.count
    rw [lintegral_count]
    exact le_tsum (fun x : Lattice m => (f x : ℝ≥0∞)) x
  refine ⟨hbound d, ?_⟩
  induction d with
  | zero => simp [autocorrelation, cubeProduct, cubeMeasure, Measure.pi_empty_univ]
  | succ d ih =>
    rw [lintegral_autocorrelation_succ μ hf.aemeasurable]
    calc
      _ ≤ (M ^ (2 ^ d : ℕ)) ^ (2 : ℕ) :=
        lintegral_pow_le (cubeMeasure μ d) _ (.of_discrete) _ (hbound d) ih _ (by decide)
      _ = _ := by simp [M, μ, pow_succ, pow_mul]

/-- q=1 is admissible for every d and positive integer p, uniformly in m and the side length. -/
theorem one_mem_functionExponents (d k n : ℕ) : 1 ∈ functionExponents d (k + 1) n := by
  refine ⟨by norm_num, ?_⟩
  intro m f _
  let μ : Measure (Lattice m) := Measure.count
  let M : ℝ≥0∞ := ∫⁻ x, (f x : ℝ≥0∞) ∂μ
  obtain ⟨hpoint, hint⟩ := lattice_autocorrelation_bounds m f d
  have h := lintegral_pow_le (cubeMeasure μ d) _ (.of_discrete) _ hpoint hint (k + 1) (by omega)
  have h' := ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1 / ((k + 1 : ℕ) : ℝ)))
    (by positivity : 0 ≤ 1 / (2 : ℝ) ^ d)
  simp only [gowers, lp, ENNReal.rpow_natCast, one_div_one, ENNReal.rpow_one, liftNN]
  refine h'.trans_eq ?_
  have cancel (x : ℝ≥0∞) (j : ℕ) (hj : 0 < j) : (x^j) ^ (1/(j:ℝ)) = x := by
    rw [← ENNReal.rpow_natCast, one_div, ENNReal.rpow_rpow_inv (by positivity : (j:ℝ) ≠ 0)]
  rw [cancel _ (k + 1) (by omega)]
  simpa using cancel M (2 ^ d) (by positivity)

/-- Finite support turns every positive q-norm into a finite continuous expression in q. -/
theorem lp_count_finite {m : ℕ} (A : Finset (Lattice m)) (f : Lattice m → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) {q : ℝ} (hq : 0 < q) :
    lp Measure.count q (liftNN f) = (((∑ x ∈ A, f x ^ q) ^ (1 / q) : ℝ≥0) : ℝ≥0∞) := by
  rw [lp, lintegral_count, tsum_eq_sum (s := A), ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  · simp [liftNN, ENNReal.coe_rpow_of_nonneg _ hq.le]
  · intro x hx
    simp [liftNN, hf x hx, hq]

theorem functional_exponent_upper {d k n : ℕ} (hn : 2 ≤ n) {q : ℝ}
    (hq : q ∈ functionExponents d (k + 1) n) :
    q ≤ (2:ℝ) ^ d * (k + 1 : ℕ) / criticalT d (k + 1) n := by
  have hmin := criticalT_isLeast d k n hn
  have hh := hmin.2 (setExponent_of_functionExponent d k n hq)
  rw [le_div_iff₀ hq.1] at hh
  rw [le_div_iff₀ hmin.1.1]
  simpa only [mul_comm] using hh

/-- The maximizing exponent in (1.10) is attained for all d, p=k+1, n≥2. -/
theorem criticalQ_isGreatest (d k n : ℕ) (hn : 2 ≤ n) :
    IsGreatest (functionExponents d (k + 1) n) (criticalQ d (k + 1) n) := by
  let S := functionExponents d (k + 1) n
  have hS : S.Nonempty := ⟨1, one_mem_functionExponents d k n⟩
  have hbounded : BddAbove S := ⟨_, fun _ hq => functional_exponent_upper hn hq⟩
  let q := criticalQ d (k + 1) n
  have hq : 0 < q := zero_lt_one.trans_le (le_csSup hbounded (one_mem_functionExponents d k n))
  obtain ⟨u, _, hu, hmem⟩ := exists_seq_tendsto_sSup hS hbounded
  refine ⟨⟨hq, ?_⟩, fun _ ht => le_csSup hbounded ht⟩
  intro m f hf
  let B := box m n
  have hu' : Tendsto u atTop (𝓝 q) := hu
  have hs : Tendsto (fun i => ∑ x ∈ B, f x ^ u i) atTop (𝓝 (∑ x ∈ B, f x ^ q)) :=
    tendsto_finsetSum B fun _ _ => tendsto_const_nhds.nnrpow hu' (Or.inr hq)
  have hnorm := hs.nnrpow (tendsto_const_nhds.div hu' hq.ne') (Or.inr (one_div_pos.mpr hq))
  rw [lp_count_finite B f hf hq]
  apply ge_of_tendsto (ENNReal.continuous_coe.continuousAt.tendsto.comp hnorm)
  apply Eventually.of_forall
  intro i
  have hi := (hmem i).2 m f hf
  change _ ≤ (((∑ x ∈ B, f x ^ u i) ^ (1 / u i) : ℝ≥0) : ℝ≥0∞)
  simpa only [lp_count_finite B f hf (hmem i).1] using hi

/-- One side of (1.12), obtained by testing on indicators and maximizing in q. -/
theorem criticalQ_mul_criticalT_le (d k n : ℕ) (hn : 2 ≤ n) :
    criticalQ d (k + 1) n * criticalT d (k + 1) n ≤ (2:ℝ) ^ d * (k + 1 : ℕ) := by
  exact (le_div_iff₀ (criticalT_isLeast d k n hn).1.1).mp
    (functional_exponent_upper hn (criticalQ_isGreatest d k n hn).1)

theorem binary_criticalQ_two_two_le : criticalQ 2 2 2 ≤ 8 / 3 := by
  have h := criticalQ_mul_criticalT_le 2 1 2 (by decide)
  norm_num [binary_criticalT_two_two] at h ⊢
  linarith

/-- The marginal identity identifies adjacent degrees, for actual finite energies. -/
theorem energy_succ_one (m d : ℕ) (A : Finset (Lattice m)) :
    energy (d + 1) 1 A = energy d 2 A := by
  have hm := gowers_one_succ_eq_gowers_two (Measure.count : Measure (Lattice m))
    (Measurable.of_discrete (f := finIndicator A)).aemeasurable d
  have h₁ := gowers_finIndicator (d + 1) 0 A
  have h₂ := gowers_finIndicator d 1 A
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, mul_one] at h₁ h₂
  rw [h₁, h₂, pow_succ] at hm
  exact_mod_cast (ENNReal.rpow_left_injective (by positivity : 1 / ((2 : ℝ)^d * 2) ≠ 0) hm)

/-- Both critical exponents agree for parameters (d+1,1) and (d,2), respectively. -/
theorem critical_succ_one (d n : ℕ) :
    criticalT (d + 1) 1 n = criticalT d 2 n ∧ criticalQ (d + 1) 1 n = criticalQ d 2 n := by
  constructor
  · simp only [criticalT, setExponents, energy_succ_one]
  · unfold criticalQ functionExponents
    simp only [Nat.cast_one, Nat.cast_ofNat,
      gowers_one_succ_eq_gowers_two Measure.count Measurable.of_discrete.aemeasurable]

/-- To obtain the uniform strict upper bound in (1.13) it suffices to do so for
the single additive-energy exponent t₂,₁,ₙ. -/
theorem criticalT_le_additive_energy (j k n : ℕ) :
    criticalT (j + 2) (k + 1) n ≤ criticalT 2 1 n + j + k := by
  have hstep (r : ℕ) : criticalT (r + 1) 1 n ≤ criticalT r 1 n + 1 := by
    rw [(critical_succ_one r n).1]
    simpa using criticalT_le_shift r 1 n
  have hd : criticalT (j + 2) 1 n ≤ criticalT 2 1 n + j := by
    induction j with
    | zero => simp
    | succ a ih =>
      have h := hstep (a + 2)
      push_cast
      linarith
  exact (criticalT_le_shift (j + 2) k n).trans (by linarith)


end LpGowers.Discrete
