module

public import LpGowers.ExtendedHolder
public import LpGowers.PowerTransfer
public import LpGowers.YoungPlateau
import Mathlib.Tactic

/-! # The approximate Euler relation from Hölder stability

A nonnegative input and a subnormalized dual function with nearly maximal
pairing are close after applying the conjugate power to the dual function.
The threshold is uniform in the measure and in the functions. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology
namespace LpGowers

/-- Stability of the inverse norming map on the positive cone of L^q.
The q and q' masses are only required to be ≤ 1. -/
theorem near_norming_power {q v : ℝ} (hq : 1 < q) (hv : 1 < v)
    (hc : 1/q + 1/v = 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f b : X → ℝ≥0),
      AEMeasurable f μ → AEMeasurable b μ →
      (∫⁻ x, (f x : ℝ≥0∞)^q ∂μ) ≤ 1 → (∫⁻ x, (b x : ℝ≥0∞)^v ∂μ) ≤ 1 →
      ENNReal.ofReal (1-ε) ≤ (∫⁻ x, (f x : ℝ≥0∞) * b x ∂μ) →
      lpDist μ q f (fun x => b x ^ (v-1)) ≤ ENNReal.ofReal η := by
  classical
  have hq0 := zero_lt_one.trans hq
  have hv0 := zero_lt_one.trans hv
  let w : Fin 2 → ℝ := ![1/q,1/v]
  have hw i : 0 < w i := by fin_cases i <;> simp [w, hq0, hv0]
  have hws : ∑ i, w i = 1 := by simpa [Fin.sum_univ_two,w] using hc
  have he := Real.rpow_pos_of_pos hη q
  obtain ⟨δ,hd,H⟩ := holder_stability_ennreal w hw hws he
  refine ⟨δ,hd,?_⟩
  intro ε hε hεδ X _ μ f b hf hb hfm hbm hnear
  let F := fun x => f x ^ q
  let B := fun x => b x ^ v
  let u : Fin 2 → X → ℝ≥0∞ := ![liftNN F,liftNN B]
  have hu i : AEMeasurable (u i) μ := by
    fin_cases i
    · exact measurable_coe_nnreal_ennreal.comp_aemeasurable (hf.pow_const q)
    · exact measurable_coe_nnreal_ennreal.comp_aemeasurable (hb.pow_const v)
  have hunit i : (∫⁻ x, u i x ∂μ) ≤ 1 := by
    fin_cases i
    · simpa [u,liftNN,F,ENNReal.coe_rpow_of_nonneg _ hq0.le] using hfm
    · simpa [u,liftNN,B,ENNReal.coe_rpow_of_nonneg _ hv0.le] using hbm
  have hprod x : (∏ j, (u j x)^w j) = (f x : ℝ≥0∞)*b x := by
    simp [Fin.prod_univ_two,u,w,liftNN,F,B,ENNReal.coe_rpow_of_nonneg _ hq0.le,
      ENNReal.coe_rpow_of_nonneg _ hv0.le,← ENNReal.rpow_mul,hq0.ne',hv0.ne']
  have hnorm := (H ε hε hεδ μ u hu hunit (by simpa only [hprod] using hnear) 0).2 1
  change l1DensityError μ (liftNN F) (liftNN B) ≤ ENNReal.ofReal (η ^ q) at hnorm
  rw [← lpDist_one_eq_densityError] at hnorm
  have hvc : v * (1/q) = v-1 := by
    rw [show 1/q = 1-1/v by linarith]
    field_simp
  have hp := lpDist_rpow_sublinear μ zero_lt_one (one_div_pos.mpr hq0)
    ((div_le_iff₀ hq0).2 (by simpa using hq.le)) F B
  have hh := hp.trans (ENNReal.rpow_le_rpow hnorm (one_div_nonneg.mpr hq0.le))
  rw [← ENNReal.ofReal_rpow_of_nonneg hη.le hq0.le,← ENNReal.rpow_mul,
    mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at hh
  simpa [F,B,← NNReal.rpow_mul,show v * q⁻¹ = v-1 by simpa using hvc,hq0.ne'] using hh

end LpGowers
