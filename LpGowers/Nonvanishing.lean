module

public import LpGowers.LebesgueProofs
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Nonvanishing for arbitrary finite positive outer exponents, §2. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace LpGowers

theorem lp_eq_zero_iff {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ} (hp : 0 < p) :
    lp ν p F = 0 ↔ F =ᵐ[ν] 0 := by
  rw [lp, ENNReal.rpow_eq_zero_iff_of_pos (by positivity), lintegral_eq_zero_iff' (hF.pow_const p)]
  change (∀ᵐ x ∂ν, F x ^ p = 0) ↔ ∀ᵐ x ∂ν, F x = 0
  simp only [ENNReal.rpow_eq_zero_iff_of_pos hp]

theorem gowers_eq_zero_iff {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    (d : ℕ) {p : ℝ} (hp : 0 < p) {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ d p f = 0 ↔ f =ᵐ[μ] 0 := by
  have reduce (k : ℕ) (q : ℝ) (hq : 0 < q) :
      gowers μ k q f = 0 ↔ autocorrelation μ k f =ᵐ[cubeMeasure μ k] 0 := by
    rw [gowers, ENNReal.rpow_eq_zero_iff_of_pos (by positivity),
      lp_eq_zero_iff _ (measurable_autocorrelation_of_aemeasurable μ k hf).aemeasurable hq]
  induction d generalizing p with
  | zero =>
    simp only [gowers, lp, autocorrelation, cubeProduct, cubeMeasure, lintegral_const,
      Measure.pi_empty_univ, mul_one, pow_zero, div_one, ENNReal.rpow_one]
    rw [one_div, ENNReal.rpow_rpow_inv hp.ne', lintegral_eq_zero_iff' (by fun_prop)]
    change (∀ᵐ x ∂μ, (f x : ℝ≥0∞) = 0) ↔ ∀ᵐ x ∂μ, f x = 0
    simp
  | succ k ih =>
    rw [reduce (k + 1) p hp, ← reduce (k + 1) 1 (by norm_num),
      gowers_one_succ_eq_gowers_two μ hf]
    exact ih (p := 2) (by norm_num)

end LpGowers
