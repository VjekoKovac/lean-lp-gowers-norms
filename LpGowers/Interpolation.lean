module

public import LpGowers.Defs
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic

/-! Finite-exponent interpolation used in §§2, 3 and 6 of Kovač–Rogers.
The proof uses Mathlib's integral form of weighted Hölder. -/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace LpGowers

/-- Log-convexity on any measure space, for all finite positive exponents,
including quasi-norms and infinite values of the integrals. -/
theorem lp_interpolate {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {p a b θ : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (h : 1 / p = θ / a + (1 - θ) / b) :
    lp μ p F ≤ lp μ a F ^ θ * lp μ b F ^ (1 - θ) := by
  let s := p * θ / a
  let t := p * (1 - θ) / b
  have hθ₁ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ'
  have hs : 0 ≤ s := div_nonneg (mul_nonneg hp.le hθ) ha.le
  have ht : 0 ≤ t := div_nonneg (mul_nonneg hp.le hθ₁) hb.le
  have hst : s + t = 1 := by
    calc
      s + t = p * (θ / a + (1 - θ) / b) := by dsimp [s, t]; ring
      _ = 1 := by rw [← h]; field_simp
  have hexp : a * s + b * t = p := by dsimp [s, t]; field_simp; ring
  have hv (x : X) : F x ^ p = (F x ^ a) ^ s * (F x ^ b) ^ t := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha.le hs) (mul_nonneg hb.le ht), hexp]
  have hm := ENNReal.lintegral_mul_norm_pow_le (hF.pow_const a) (hF.pow_const b) hs ht hst
  have hlin : (∫⁻ x, F x ^ p ∂μ) ≤
      (∫⁻ x, F x ^ a ∂μ) ^ s * (∫⁻ x, F x ^ b ∂μ) ^ t := by
    simpa only [hv] using hm
  have hroot : 0 ≤ 1 / p := by positivity
  have hsa : s * (1 / p) = (1 / a) * θ := by dsimp [s]; field_simp
  have htb : t * (1 / p) = (1 / b) * (1 - θ) := by dsimp [t]; field_simp
  unfold lp
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hroot, ← ENNReal.rpow_mul, hsa, htb]
    using ENNReal.rpow_le_rpow hlin hroot

/-- Equation (2.4), with finite exponents. The measurability hypothesis is
on the function to which Hölder is applied. -/
theorem gowers_interpolate {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (d : ℕ) (f : G → ℝ≥0)
    (hf : AEMeasurable (autocorrelation μ d f) (cubeMeasure μ d))
    {p a b θ : ℝ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ)
    (hθ' : θ ≤ 1) (h : 1 / p = θ / a + (1 - θ) / b) :
    gowers μ d p f ≤ gowers μ d a f ^ θ * gowers μ d b f ^ (1 - θ) := by
  have hr : 0 ≤ 1 / (2 : ℝ) ^ d := by positivity
  have hI := lp_interpolate (cubeMeasure μ d) hf hp ha hb hθ hθ' h
  unfold gowers
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul,
    mul_comm θ (1 / (2 : ℝ) ^ d), mul_comm (1 - θ) (1 / (2 : ℝ) ^ d)]
    using ENNReal.rpow_le_rpow hI hr

end LpGowers
