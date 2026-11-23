module

public import LpGowers.Lebesgue
public import LpGowers.DegreeTwo
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Subgroup indicators and the interpolation parameters of Theorem 1.2

We use the lower integrals of indicator functions from mathlib and the
rectangle formula for the product measure. In particular the exact formula
for a subgroup is valid also when its measure is zero or infinite. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal BigOperators Classical

noncomputable section

namespace LpGowers

variable {G : Type*} [AddCommGroup G]

/-- All vertices lie in a subgroup precisely when the base and every increment do. -/
theorem cubeProduct_subgroup_indicator (H : AddSubgroup G) (d : ℕ)
    (h : Fin d → G) (x : G) :
    cubeProduct d ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) h x =
      (if x ∈ H ∧ ∀ i, h i ∈ H then 1 else 0 : ℝ≥0∞) := by
  classical
  induction d generalizing x with
  | zero =>
      by_cases hx : x ∈ H <;> simp [cubeProduct, Set.indicator, hx]
  | succ d ih =>
      rw [cubeProduct, ih, ih]
      have hsum (hx : x ∈ H) : x + h 0 ∈ H ↔ h 0 ∈ H := by
        exact H.add_mem_cancel_left hx
      by_cases hx : x ∈ H
      · simp only [hx, true_and, hsum hx, Fin.forall_fin_succ, Fin.tail]
        split_ifs <;> simp_all
      · simp [hx]

variable [MeasurableSpace G]

/-- The pointwise subgroup autocorrelation identity in §2. -/
theorem autocorrelation_subgroup_indicator (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (d : ℕ) (h : Fin d → G) :
    autocorrelation μ d ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) h =
      (Set.univ.pi (fun _ : Fin d => (H : Set G))).indicator
        (fun _ => μ (H : Set G)) h := by
  classical
  unfold autocorrelation
  simp_rw [cubeProduct_subgroup_indicator]
  by_cases hh : ∀ i, h i ∈ H
  · have hmem : h ∈ Set.univ.pi (fun _ : Fin d => (H : Set G)) := by simpa using hh
    rw [Set.indicator_of_mem hmem]
    simpa [hh, Set.indicator] using
      (lintegral_indicator_const (μ := μ) hH (1 : ℝ≥0∞))
  · simp [hh]

/-- Exact `U^{d,p}` value of a subgroup indicator, equation (2.3).
The power simplifies without dividing by the measure of the subgroup. -/
theorem gowers_subgroup_indicator (μ : Measure G) [SigmaFinite μ] (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) =
      μ (H : Set G) ^ (((d : ℝ) + p) / ((2 : ℝ) ^ d * p)) := by
  classical
  let box := Set.univ.pi (fun _ : Fin d => (H : Set G))
  have hbox : MeasurableSet box :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => hH)
  have hvolume : cubeMeasure μ d box = μ (H : Set G) ^ d := by
    simp [box, cubeMeasure]
  have hpow : ∀ h, autocorrelation μ d
      ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) h ^ p =
      box.indicator (fun _ => μ (H : Set G) ^ p) h := by
    intro h
    rw [autocorrelation_subgroup_indicator μ H hH]
    by_cases hh : h ∈ box
    · change box.indicator (fun _ => μ (H : Set G)) h ^ p =
          box.indicator (fun _ => μ (H : Set G) ^ p) h
      simp [Set.indicator_of_mem hh]
    · change box.indicator (fun _ => μ (H : Set G)) h ^ p =
          box.indicator (fun _ => μ (H : Set G) ^ p) h
      simp [Set.indicator_of_notMem hh, ENNReal.zero_rpow_of_pos hp]
  unfold gowers lp
  simp_rw [hpow]
  rw [lintegral_indicator_const hbox, hvolume, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_add_of_nonneg _ _ hp.le (Nat.cast_nonneg _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  congr 1
  ring

/-- The endpoint used in the induction corresponds to an input `L¹` bound. -/
theorem criticalExponent_lowerEndpoint {d : ℕ} (hd : 2 ≤ d) :
    criticalExponent d (lowerEndpoint d) = 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow : 1 < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) (by omega)
  unfold criticalExponent lowerEndpoint
  norm_num only [Nat.cast_ofNat]
  have hp : 0 < (d : ℝ) / (2 ^ d - 1) := div_pos hd' (by linarith)
  apply (div_eq_iff (ne_of_gt (add_pos hd' hp))).2
  field_simp [(sub_pos.mpr hpow).ne']
  ring

/-- The two factors in the proof of the interior Lebesgue estimate
reconstruct the input with these precise exponents. -/
theorem interpolation_exponents {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hp : lowerEndpoint d < p) :
    let θ := (d : ℝ) / (p * (2 ^ d - 1))
    0 < θ ∧ θ < 1 ∧ θ * criticalExponent d p + (1 - θ) * (p / (d + p)) = 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow : 1 < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < (2 : ℝ) ^ d - 1 := by linarith
  have hp' : 0 < p := lt_trans (div_pos hd' hden) hp
  have hupper : (d : ℝ) < p * (2 ^ d - 1) := (div_lt_iff₀ hden).mp hp
  dsimp
  refine ⟨div_pos hd' (mul_pos hp' hden), (div_lt_one (mul_pos hp' hden)).mpr hupper, ?_⟩
  unfold criticalExponent
  field_simp [ne_of_gt hp', ne_of_gt hden, ne_of_gt (add_pos hd' hp')]
  ring

section InfiniteEndpoint

variable [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant]

/-- Completion-measurability in the base point, for every fixed tuple of increments. -/
theorem aemeasurable_cubeProduct_fixed {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (d : ℕ) (h : Fin d → G) : AEMeasurable (cubeProduct d f h) μ := by
  induction d with
  | zero => exact hf.coe_nnreal_ennreal
  | succ d ih =>
      have hu := ih (Fin.tail h)
      exact hu.mul (hu.comp_quasiMeasurePreserving
        (measurePreserving_add_right μ (h 0)).quasiMeasurePreserving)

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- Convex geometric means commute with forming cube products. -/
theorem cubeProduct_geometric (d : ℕ) (f g : G → ℝ≥0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Fin d → G) (x : G) :
    cubeProduct d (fun y => f y ^ a * g y ^ b) h x =
      cubeProduct d f h x ^ a * cubeProduct d g h x ^ b := by
  induction d generalizing x with
  | zero => simp [cubeProduct, ENNReal.coe_rpow_of_nonneg, ha, hb]
  | succ d ih =>
      simp only [cubeProduct, ih, ENNReal.mul_rpow_of_nonneg _ _ ha,
        ENNReal.mul_rpow_of_nonneg _ _ hb]
      ac_rfl

/-- Hölder in the base point, the first step of equation (2.5). -/
theorem autocorrelation_geometric_le {f g : G → ℝ≥0}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (d : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h : Fin d → G) :
    autocorrelation μ d (fun x => f x ^ a * g x ^ b) h ≤
      autocorrelation μ d f h ^ a * autocorrelation μ d g h ^ b := by
  unfold autocorrelation
  simp_rw [cubeProduct_geometric d f g ha hb]
  exact ENNReal.lintegral_mul_norm_pow_le (aemeasurable_cubeProduct_fixed μ hf d h)
    (aemeasurable_cubeProduct_fixed μ hg d h) ha hb hab

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
private theorem cubeProduct_sq (d : ℕ) (f : G → ℝ≥0) (h : Fin d → G) (x : G) :
    cubeProduct d (fun y => f y ^ 2) h x = cubeProduct d f h x ^ 2 := by
  induction d generalizing x with
  | zero => simp [cubeProduct]
  | succ d ih => simp only [cubeProduct, ih, mul_pow]

/-- The pointwise infinity-endpoint bound used to interpolate the interior
Lebesgue estimate. The proof applies Cauchy–Schwarz to the two faces of the
cube and uses translation invariance to identify their square integrals. -/
theorem autocorrelation_le_lintegral_pow (d : ℕ) {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) (h : Fin d → G) :
    autocorrelation μ d f h ≤ ∫⁻ x, (f x : ℝ≥0∞) ^ (2 ^ d : ℕ) ∂μ := by
  induction d generalizing f with
  | zero => simp [autocorrelation, cubeProduct]
  | succ d ih =>
      let u := cubeProduct d f (Fin.tail h)
      have hu := aemeasurable_cubeProduct_fixed μ hf d (Fin.tail h)
      have hv := hu.comp_quasiMeasurePreserving
        (measurePreserving_add_right μ (h 0)).quasiMeasurePreserving
      have hconj : Real.HolderConjugate 2 2 :=
        Real.holderConjugate_iff.mpr (by norm_num)
      have hc := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hu hv
      change (∫⁻ x, u x * u (x + h 0) ∂μ) ≤ _ at hc
      change (∫⁻ x, u x * u (x + h 0) ∂μ) ≤ _
      have htrans : (∫⁻ x, u (x + h 0) ^ (2 : ℝ) ∂μ) =
          ∫⁻ x, u x ^ (2 : ℝ) ∂μ := lintegral_add_right_eq_self (fun x => u x ^ (2 : ℝ)) _
      calc
        _ ≤ (∫⁻ x, u x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
              (∫⁻ x, u (x + h 0) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hc
        _ = ∫⁻ x, u x ^ (2 : ℕ) ∂μ := by
          rw [htrans, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
        _ = autocorrelation μ d (fun x => f x ^ 2) (Fin.tail h) := by
          simp only [autocorrelation, cubeProduct_sq, u]
        _ ≤ _ := (ih (hf.pow_const 2) (Fin.tail h)).trans_eq (by
          apply lintegral_congr
          intro x
          rw [ENNReal.coe_pow, ← pow_mul, pow_succ, Nat.mul_comm 2])

/-- Section 3, passage from the lower endpoint to every interior exponent.
The sole estimate assumed here is the same-degree `L¹` endpoint, applied to
`f^q`. This isolates the exact remaining degree-lowering input. -/
theorem lebesgue_bound_of_lower_endpoint {d : ℕ} (hd : 2 ≤ d) {p : ℝ}
    (hp : lowerEndpoint d < p) {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (hend : ∀ F : G → ℝ≥0, AEMeasurable F μ →
      gowers μ d (lowerEndpoint d) F ≤ lp μ 1 (liftNN F)) :
    gowers μ d p f ≤ lp μ (criticalExponent d p) (liftNN f) := by
  let K : ℝ := 2 ^ d
  let e := lowerEndpoint d
  let q := criticalExponent d p
  let b := p / (d + p)
  let θ := (d : ℝ) / (p * (2 ^ d - 1))
  let F := fun x => f x ^ q
  let V := fun x => f x ^ b
  let N := ∫⁻ x, (f x : ℝ≥0∞) ^ q ∂μ
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hK : 1 < K := one_lt_pow₀ (by norm_num) (by omega)
  have he : 0 < e := div_pos hd' (sub_pos.mpr hK)
  have hp' : 0 < p := lt_trans he hp
  have hq : 0 < q := div_pos (mul_pos (by positivity) hp') (add_pos hd' hp')
  have hb : 0 < b := div_pos hp' (add_pos hd' hp')
  have ⟨hθ, hθ', hsplit⟩ := interpolation_exponents hd hp
  change 0 < θ at hθ
  change θ < 1 at hθ'
  change θ * q + (1 - θ) * b = 1 at hsplit
  have hθb : 0 ≤ 1 - θ := sub_nonneg.mpr hθ'.le
  have hprod : θ * p = e := by
    dsimp [θ, e, lowerEndpoint]; field_simp [hp'.ne', (sub_pos.mpr hK).ne']
  have hbK : b * K = q := by dsimp [b, K, q, criticalExponent]; ring
  have hfF : AEMeasurable F μ := hf.pow_const _
  have hfV : AEMeasurable V μ := hf.pow_const _
  have hF : lp μ 1 (liftNN F) = N := by
    simp [lp, liftNN, F, N, ENNReal.coe_rpow_of_nonneg _ hq.le]
  have hV : (∫⁻ x, (V x : ℝ≥0∞) ^ (2 ^ d : ℕ) ∂μ) = N := by
    apply lintegral_congr
    intro x
    dsimp only [V]
    rw [ENNReal.coe_rpow_of_nonneg _ hb.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    exact congrArg (fun v : ℝ => (f x : ℝ≥0∞) ^ v) (by simpa [K] using hbK)
  have hfg : (fun x => F x ^ θ * V x ^ (1 - θ)) = f := by
    funext x
    dsimp only [F, V]
    rw [← NNReal.rpow_mul, ← NNReal.rpow_mul,
      ← NNReal.rpow_add_of_nonneg _ (mul_nonneg hq.le hθ.le) (mul_nonneg hb.le hθb),
      mul_comm q θ, mul_comm b (1 - θ), hsplit, NNReal.rpow_one]
  have htarget : lp μ (criticalExponent d p) (liftNN f) = N ^ (1 / q) := rfl
  rw [htarget]
  by_cases htop : N = ⊤
  · rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hq)]
    exact le_top
  let A := ∫⁻ h, autocorrelation μ d F h ^ e ∂cubeMeasure μ d
  have hA : A ≤ N ^ (K * e) := by
    have h := (hend F hfF).trans_eq hF
    change (A ^ (1 / e)) ^ (1 / K) ≤ N at h
    simp only [one_div] at h
    rw [ENNReal.rpow_inv_le_iff (by positivity : 0 < K),
      ENNReal.rpow_inv_le_iff he, ← ENNReal.rpow_mul] at h
    exact h
  have hpoint (h : Fin d → G) : autocorrelation μ d f h ^ p ≤
      autocorrelation μ d F h ^ e * N ^ ((1 - θ) * p) := by
    have hbound := autocorrelation_geometric_le μ hfF hfV d hθ.le hθb (by ring) h
    rw [hfg] at hbound
    have hvr := (autocorrelation_le_lintegral_pow μ d hfV h).trans_eq hV
    have hright := ENNReal.rpow_le_rpow hvr hθb
    have hm := ENNReal.rpow_le_rpow (hbound.trans (mul_le_mul le_rfl hright zero_le zero_le)) hp'.le
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ hp'.le, ← ENNReal.rpow_mul, hprod] using hm
  have hbeta : 0 ≤ (1 - θ) * p := mul_nonneg hθb hp'.le
  have hi : (∫⁻ h, autocorrelation μ d f h ^ p ∂cubeMeasure μ d) ≤
      N ^ (K * e + (1 - θ) * p) := by
    calc
      _ ≤ ∫⁻ h, autocorrelation μ d F h ^ e * N ^ ((1 - θ) * p) ∂cubeMeasure μ d :=
        lintegral_mono hpoint
      _ = A * N ^ ((1 - θ) * p) :=
        lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hbeta htop)
      _ ≤ N ^ (K * e) * N ^ ((1 - θ) * p) := mul_le_mul hA le_rfl zero_le zero_le
      _ = _ := (ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by positivity) he.le) hbeta).symm
  have hfinal : (K * e + (1 - θ) * p) * (1 / p) * (1 / K) = 1 / q := by
    have heq : e = θ * p := hprod.symm
    rw [heq]
    have hqK : q = b * K := hbK.symm
    rw [hqK] at hsplit ⊢
    field_simp [hp'.ne', hK.le.trans_lt' (by norm_num : (0 : ℝ) < 1) |>.ne', hb.ne']
    linear_combination hsplit
  change (_ ^ (1 / p)) ^ (1 / K) ≤ _
  simpa only [← ENNReal.rpow_mul, hfinal] using
    ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow hi (one_div_nonneg.mpr hp'.le))
      (one_div_nonneg.mpr (by positivity : 0 ≤ K))

/-- The degree-one ordinary Gowers quantity is the `L¹` integral for
nonnegative functions. This supplies the starting point of the endpoint induction. -/
theorem gowers_one_one [SigmaFinite μ] {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ 1 1 f = lp μ 1 (liftNN f) := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, gowers_one_succ_eq_gowers_two μ hf]
  simp only [gowers, lp, autocorrelation, cubeProduct, pow_zero, div_one, ENNReal.rpow_one,
    lintegral_const, cubeMeasure, Measure.pi_empty_univ, mul_one, liftNN]
  rw [one_div, ENNReal.rpow_rpow_inv (by norm_num)]

/-- The complete degree-two case of Theorem 1.2(a), including the endpoint
`p = 2/3`, follows from the two-dimensional adjoint estimate. -/
theorem lebesgue_bound_degree_two [SigmaFinite μ] {p : ℝ} (hp : 2 / 3 ≤ p)
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ 2 p f ≤ lp μ (criticalExponent 2 p) (liftNN f) := by
  have he : lowerEndpoint 2 = 2 / 3 := by norm_num [lowerEndpoint]
  have hend (F : G → ℝ≥0) (hF : AEMeasurable F μ) :
      gowers μ 2 (lowerEndpoint 2) F ≤ lp μ 1 (liftNN F) := by
    rw [he]
    exact (degree_two_twoThirds μ hF).trans_eq (gowers_one_one μ hF)
  rcases (he ▸ hp : lowerEndpoint 2 ≤ p).eq_or_lt with rfl | hlt
  · rw [criticalExponent_lowerEndpoint (by decide : 2 ≤ 2)]
    exact hend f hf
  · exact lebesgue_bound_of_lower_endpoint μ (by decide) hlt hf hend

end InfiniteEndpoint

/-- The symmetric degree-lowering parameters of §3 at the lower endpoint. -/
theorem lowerEndpoint_parameters {k : ℕ} (hk : 1 ≤ k) :
    DegreeParameters k (lowerEndpoint (k + 1)) (fun _ => lowerEndpoint k)
        (fun _ => 1 / ((k : ℝ) + 1)) ∧
      DegreeForward (lowerEndpoint (k + 1)) (fun _ : Fin (k + 1) => 1 / ((k : ℝ) + 1)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpow : 1 < (2 : ℝ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
  have hpow' : 0 < (2 : ℝ) ^ (k + 1) - 1 := by rw [pow_succ]; linarith
  have hkplus : (0 : ℝ) < k + 1 := by positivity
  have hlower : (k : ℝ) + 1 + 1 ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.succ_le_of_lt (k + 1).lt_two_pow_self
  constructor
  · refine ⟨fun _ => div_pos hk' (sub_pos.mpr hpow), ?_, fun _ => ?_⟩
    · simp [Nat.cast_add, Nat.cast_one, hkplus.ne']
    · unfold lowerEndpoint
      push_cast
      rw [pow_succ]
      field_simp [hk'.ne', hkplus.ne', (sub_pos.mpr hpow).ne']
      ring
  · refine ⟨?_, ?_, fun _ => one_div_pos.mpr hkplus⟩
    · exact div_pos (by exact_mod_cast (Nat.zero_lt_succ k)) hpow'
    · apply (div_le_one hpow').mpr
      push_cast
      linarith

/-- Induction in the degree gives the complete lower-endpoint estimate from
the forward part of Theorem 1.4(a). No stability statement is used. -/
theorem lowerEndpoint_of_degreeInequalities.{u} (hD : DegreeInequalities.{u})
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (d : ℕ) (hd : 1 ≤ d) :
    gowers μ d (lowerEndpoint d) f ≤ lp μ 1 (liftNN f) := by
  induction d, hd using Nat.le_induction with
  | base =>
      rw [show lowerEndpoint 1 = 1 by norm_num [lowerEndpoint], gowers_one_one μ hf]
  | succ k hk ih =>
      obtain ⟨hparam, hfwd⟩ := lowerEndpoint_parameters hk
      have h := (hD k hk _ _ _ hparam G μ f hf).1 hfwd
      have hpow (x : ℝ≥0∞) : (x ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) = x := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        push_cast
        rw [div_mul_cancel₀ _ (by positivity : (k : ℝ) + 1 ≠ 0), ENNReal.rpow_one]
      simpa only [lowerProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        hpow] using h.trans (by
          simpa only [lowerProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            hpow] using ih)

/-- Precise dependency from Theorem 1.4(a) to Theorem 1.2(a), including the
closed endpoint and the whole positive finite exponent range above it. -/
theorem lebesgueBound_of_degreeInequalities.{u} (hD : DegreeInequalities.{u}) :
    LebesgueBound.{u} := by
  intro d hd p hp G _ _ _ _ _ _ _ _ μ _ f hf
  have hend := fun F (hF : AEMeasurable F μ) =>
    lowerEndpoint_of_degreeInequalities hD μ hF d (by omega)
  rcases hp.eq_or_lt with rfl | hlt
  · rw [criticalExponent_lowerEndpoint hd]
    exact hend f hf
  · exact lebesgue_bound_of_lower_endpoint μ hd hlt hf hend

end LpGowers
