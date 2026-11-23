module

public import LpGowers.YoungContinuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Scaling the indicator autocorrelation in inverse Young

For the critical exponent `s=2d/(d+1)`, dividing the indicator by the
`s`th root of its measure divides the autocorrelation moment by the
`(d+1)`st power of that measure.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

/-- The full indicator moment is its unit-normalized moment times `μ(E)^(d+1)`. -/
theorem indicator_moment_rescale {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (d : ℕ) (hd : 0 < d) (E : Set G) (hp : 0 < μ E) (hf : μ E ≠ ⊤) :
    let s := 2*(d:ℝ)/(d+1)
    let g := E.indicator (fun _ => (μ E).toNNReal^(-(1/s)))
    (∫⁻ t, (∫⁻ x, E.indicator (1 : G → ℝ≥0∞) x * E.indicator 1 (x+t) ∂μ)^d ∂μ) =
      (μ E)^(d+1) * ∫⁻ t, (∫⁻ x, (g x : ℝ≥0∞)*g (x+t) ∂μ) ^ (d:ℝ) ∂μ := by
  classical
  intro s g
  let b := (μ E).toNNReal
  let c := b^(1/s)
  have hD : 0 < (d : ℝ) := by exact_mod_cast hd
  have hb : 0 < b := ENNReal.toNNReal_pos hp.ne' hf
  have hc : c ≠ 0 := (NNReal.rpow_pos (p := 1/s) hb).ne'
  have hpoint (x : G) : E.indicator (1 : G → ℝ≥0∞) x = (c:ℝ≥0∞) * g x := by
    by_cases hx : x∈E
    · simp only [indicator_of_mem hx,Pi.one_apply,g,← ENNReal.coe_mul]
      change (1 : ℝ≥0∞) = ((c * b ^ (-(1/s)) : ℝ≥0) : ℝ≥0∞)
      rw [NNReal.rpow_neg]
      rw [show b^(1/s)=c from rfl,mul_inv_cancel₀ hc,ENNReal.coe_one]
    · simp [hx,g]
  have point (t : G) : (∫⁻ x, E.indicator (1 : G → ℝ≥0∞) x * E.indicator 1 (x+t) ∂μ) =
      (c:ℝ≥0∞)^2*(∫⁻ x, (g x : ℝ≥0∞)*g (x+t) ∂μ) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
    apply lintegral_congr
    intro x
    rw [hpoint,hpoint,pow_two]
    ac_rfl
  simp_rw [point,mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
  simp only [ENNReal.rpow_natCast]
  congr 1
  rw [← pow_mul, ← ENNReal.rpow_natCast,ENNReal.coe_rpow_of_ne_zero hb.ne', ← ENNReal.rpow_mul,
    ENNReal.coe_toNNReal hf, ← ENNReal.rpow_natCast]
  congr 1
  dsimp [s]
  push_cast
  field_simp

/-- Minkowski bounds the distance through a common normalized indicator. -/
theorem lpDist_triangle {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : ℝ} (hs : 1 ≤ s)
    (f g h : X → ℝ≥0) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hh : AEMeasurable h μ) :
    lpDist μ s f h ≤ lpDist μ s f g + lpDist μ s g h := by
  let u := fun x => edist (f x) (g x)
  let v := fun x => edist (g x) (h x)
  refine (le_trans ?_ (ENNReal.lintegral_Lp_add_le (hf.edist hg) (hg.edist hh) hs))
  unfold lpDist lp
  gcongr with x
  exact edist_triangle (f x) (g x) (h x)

end LpGowers
