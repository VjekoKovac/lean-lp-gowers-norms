module

public import LpGowers.Lebesgue
public import LpGowers.Scaling
import LpGowers.Nonvanishing
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic

/-! # Unit-mass normalization in Theorem 1.2(b)

The normalized assertion uses a unit critical moment. Scaling returns the
exact relative error and the specified amplitude of the coset profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LpGowers

def NormalizedLebesgueStability : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ p : ℝ, lowerEndpoint d < p →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0), AEMeasurable f μ →
      (∫⁻ x, (f x : ℝ≥0∞) ^ criticalExponent d p ∂μ) = 1 →
      ENNReal.ofReal (1 - ε) ≤ gowers μ d p f →
      ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
        lpDist μ (criticalExponent d p) f (cosetProfile μ (criticalExponent d p) 1 H x₀) ≤
          ENNReal.ofReal η

theorem lpDist_smul_input {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℝ≥0) (f g : X → ℝ≥0) {q : ℝ} (hq : 0 < q) :
    lpDist μ q (fun x => c * f x) (fun x => c * g x) = (c : ℝ≥0∞) * lpDist μ q f g := by
  have ed (x : X) : edist (c * f x) (c * g x) = (c : ℝ≥0∞) * edist (f x) (g x) := by
    simp only [edist_dist, NNReal.dist_eq, NNReal.coe_mul, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (NNReal.coe_nonneg c), ENNReal.ofReal_mul (NNReal.coe_nonneg c),
      ENNReal.ofReal_coe_nnreal]
  simp only [lpDist, ed, lp_const_mul _ _ _ ENNReal.coe_ne_top hq]

theorem cosetProfile_smul {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (q : ℝ) (c : ℝ≥0) (N : ℝ≥0∞) (H : AddSubgroup G) (x₀ : G) :
    cosetProfile μ q ((c : ℝ≥0∞) * N) H x₀ = fun x => c * cosetProfile μ q N H x₀ x := by
  classical
  funext x
  by_cases hx : x - x₀ ∈ H <;> simp [cosetProfile, hx, div_eq_mul_inv, mul_assoc]

section Cosets
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]

omit [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [μ.IsAddHaarMeasure] in
theorem cosetProfile_unit_rpow (r γ : ℝ) (hr : 0 < r) (hγ : 0 < γ) (H : AddSubgroup G)
    (x₀ : G) (_hc : IsCompact (H : Set G)) (_ho : IsOpen (H : Set G)) :
    (fun y => cosetProfile μ r 1 H x₀ y ^ γ) = cosetProfile μ (r/γ) 1 H x₀ := by
  classical
  funext x
  by_cases hx : x - x₀ ∈ H
  · simp only [cosetProfile, hx, ite_true, one_div, ENNReal.toNNReal_inv, ENNReal.toNNReal_rpow,
      NNReal.inv_rpow, ← NNReal.rpow_mul]
    congr 2
    field_simp
  · simp [cosetProfile, hx, NNReal.zero_rpow hγ.ne']

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem cosetProfile_unit_moment (r : ℝ) (hr : 0 < r) (H : AddSubgroup G) (x₀ : G)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H : Set G)) :
    (∫⁻ x, (cosetProfile μ r 1 H x₀ x : ℝ≥0∞) ^ r ∂μ) = 1 := by
  classical
  let m := μ (H : Set G)
  have hm0 : m ≠ 0 := (ho.measure_pos μ ⟨0, H.zero_mem⟩).ne'
  have hmt : m ≠ ⊤ := hc.measure_lt_top.ne
  have hv : (1 / m^(1/r)) ≠ ⊤ := by
    rw [one_div, ENNReal.inv_ne_top]
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hm0) hmt).ne'
  have he (x) : (cosetProfile μ r 1 H x₀ x : ℝ≥0∞)^r =
      (H : Set G).indicator (fun _ => m⁻¹) (x + -x₀) := by
    by_cases hx : x - x₀ ∈ H
    · have hxx : x + -x₀ ∈ (H : Set G) := by
        change x + -x₀ ∈ H
        rw [← sub_eq_add_neg]
        exact hx
      simp only [cosetProfile, hx, ite_true, Set.indicator_of_mem hxx]
      change (↑((1/m^(1/r)).toNNReal) : ℝ≥0∞)^r = m⁻¹
      rw [ENNReal.coe_toNNReal hv, one_div, ENNReal.inv_rpow, ← ENNReal.rpow_mul]
      simp [hr.ne']
    · simp [cosetProfile, hx, ← sub_eq_add_neg, ENNReal.zero_rpow_of_pos hr]
  simp_rw [he]
  rw [lintegral_add_right_eq_self, lintegral_indicator ho.measurableSet, setLIntegral_const,
    ENNReal.inv_mul_cancel hm0 hmt]

end Cosets


/-- Positive finite critical norm gives an amplitude times a function of
unit critical moment, for finite positive `q` on an arbitrary measure space. -/
theorem exists_unit_amplitude {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (q : ℝ) (hq : 0 < q) (f : G → ℝ≥0) (hf : AEMeasurable f μ)
    (hnonzero : ¬ f =ᵐ[μ] fun _ => 0) (hNfin : lp μ q (liftNN f) < ⊤) :
    ∃ (a : ℝ≥0) (F : G → ℝ≥0), 0 < a ∧ (a : ℝ≥0∞) = lp μ q (liftNN f) ∧
      AEMeasurable F μ ∧ (∫⁻ x, (F x : ℝ≥0∞)^q ∂μ) = 1 ∧ (fun x => a * F x) = f := by
  let N := lp μ q (liftNN f)
  have hNzero : N ≠ 0 := by
    intro h
    have hz := (lp_eq_zero_iff μ ((measurable_coe_nnreal_ennreal.comp_aemeasurable hf) :
      AEMeasurable (liftNN f) μ) hq).mp h
    apply hnonzero
    filter_upwards [hz] with x hx
    simpa [liftNN] using hx
  let a := N.toNNReal
  have ha : (a : ℝ≥0∞) = N := ENNReal.coe_toNNReal hNfin.ne
  have ha0 : a ≠ 0 := by intro h; exact hNzero (ha.symm.trans (by simp [h]))
  let F : G → ℝ≥0 := fun x => a⁻¹ * f x
  have hF : AEMeasurable F μ := aemeasurable_const.mul hf
  have hFN : lp μ q (liftNN F) = 1 := by
    change lp μ q (fun x => ((a⁻¹ * f x : ℝ≥0) : ℝ≥0∞)) = 1
    simp_rw [ENNReal.coe_mul]
    rw [lp_const_mul _ _ _ ENNReal.coe_ne_top hq, ENNReal.coe_inv ha0, ha]
    exact ENNReal.inv_mul_cancel hNzero hNfin.ne
  have hmoment : (∫⁻ x, (F x : ℝ≥0∞)^q ∂μ) = 1 := by
    have := congrArg (fun z : ℝ≥0∞ => z^q) hFN
    simpa only [lp, liftNN, one_div, ENNReal.rpow_inv_rpow hq.ne', ENNReal.one_rpow] using this
  have hfscale : (fun x => a * F x) = f := by
    funext x
    simp [F, ha0]
  exact ⟨a,F,pos_iff_ne_zero.mpr ha0,ha,hF,hmoment,hfscale⟩

/-- Undo the normalization at the start of §3, preserving the same uniform
threshold δ and the exact coefficient multiplying the coset indicator. -/
theorem lebesgueStability_of_unit.{u} (hunit : NormalizedLebesgueStability.{u}) :
    LebesgueStability.{u} := by
  intro d hd p hep η hη
  obtain ⟨δ, hδ, Hunit⟩ := hunit d hd p hep η hη
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ G _ _ _ _ _ _ _ _ μ _ f hf hnonzero
  let q := criticalExponent d p
  let N := lp μ q (liftNN f)
  change N < ⊤ → ENNReal.ofReal (1-ε) * N ≤ gowers μ d p f → _
  intro hNfin hnear
  have hp : 0 < p := by
    have hpow : 1 < (2 : ℝ)^d := one_lt_pow₀ (by norm_num) (by omega)
    have he : 0 < lowerEndpoint d := by unfold lowerEndpoint; exact div_pos (by exact_mod_cast (by omega : 0 < d)) (sub_pos.mpr hpow)
    exact he.trans hep
  have hq : 0 < q := by unfold q criticalExponent; positivity
  obtain ⟨a,F,ha0,ha,hF,hmoment,hfscale⟩ := exists_unit_amplitude μ q hq f hf hnonzero hNfin
  change (a : ℝ≥0∞) = N at ha
  have hFnear : ENNReal.ofReal (1-ε) ≤ gowers μ d p F := by
    have hn := hnear
    rw [← hfscale, gowers_smul_input μ a d F hp] at hn
    change ENNReal.ofReal (1-ε) * N ≤ (a : ℝ≥0∞) * gowers μ d p F at hn
    rw [← ha, mul_comm (ENNReal.ofReal (1-ε))] at hn
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast ha0.ne') ENNReal.coe_ne_top).mp hn
  obtain ⟨H, x₀, hc, ho, hclose⟩ := Hunit ε hε hεδ G μ F hF hmoment hFnear
  refine ⟨H, x₀, hc, ho, ?_⟩
  have hprofile : cosetProfile μ q N H x₀ = fun x => a * cosetProfile μ q 1 H x₀ x := by
    simpa [ha] using cosetProfile_smul μ q a 1 H x₀
  change lpDist μ q f (cosetProfile μ q N H x₀) ≤ ENNReal.ofReal η * N
  rw [← hfscale, hprofile, lpDist_smul_input μ a F _ hq, ha, mul_comm (ENNReal.ofReal η)]
  exact mul_le_mul_right hclose _

end LpGowers
