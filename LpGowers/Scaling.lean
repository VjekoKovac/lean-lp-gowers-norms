module

public import LpGowers.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic

/-! Two homogeneities used in the normalization of §6. The input and
the measure can be rescaled independently. -/

@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

theorem cubeMeasure_smul {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] (r : ℝ≥0) (d : ℕ) :
    cubeMeasure (r • μ) d = (r ^ d) • cubeMeasure μ d := by
  unfold cubeMeasure
  apply Measure.pi_eq
  intro s _
  simp [Finset.prod_mul_distrib]
  change ((r ^ d : ℝ≥0) : ℝ≥0∞) * _ = _
  rw [ENNReal.coe_pow]

theorem cubeProduct_smul {G : Type*} [AddCommMonoid G] (r : ℝ≥0) (d : ℕ)
    (f : G → ℝ≥0) (h : Fin d → G) (x : G) :
    cubeProduct d (fun y => r * f y) h x =
      (r : ℝ≥0∞) ^ (2 ^ d : ℕ) * cubeProduct d f h x := by
  induction d generalizing x with
  | zero => simp [cubeProduct]
  | succ d ih =>
    simp only [cubeProduct, ih, pow_succ (2 : ℕ), pow_mul, pow_two]
    ac_rfl

/-- Multiplying an extended function by a finite constant multiplies its Lᵖ functional. -/
theorem lp_const_mul {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (F : X → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) {p : ℝ} (hp : 0 < p) :
    lp ν p (fun x => c * F x) = c * lp ν p F := by
  have hp' : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hc
  unfold lp
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ hp', ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Rescaling the input amplitude. -/
theorem gowers_smul_input {G : Type*} [MeasurableSpace G] [AddCommMonoid G] (μ : Measure G)
    (r : ℝ≥0) (d : ℕ) (f : G → ℝ≥0) {p : ℝ} (hp : 0 < p) :
    gowers μ d p (fun x => r * f x) = (r : ℝ≥0∞) * gowers μ d p f := by
  let c : ℝ≥0∞ := (r : ℝ≥0∞) ^ (2 ^ d : ℕ)
  have hc : c ≠ ⊤ := by dsimp [c]; finiteness
  have hR : autocorrelation μ d (fun x => r * f x) =
      fun h => c * autocorrelation μ d f h := by
    funext h
    unfold autocorrelation
    simp_rw [cubeProduct_smul]
    exact lintegral_const_mul' c _ hc
  rw [gowers, hR, lp_const_mul _ _ c hc hp,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  unfold c
  rw [← ENNReal.rpow_natCast_mul]
  norm_num [gowers]

/-- Homogeneity of U^{d,p} in the measure. This explains the exponent
(d+p)/(2^d p) when the Haar measure is renormalized. -/
theorem gowers_smul_measure {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) [SigmaFinite μ] (r : ℝ≥0) (d : ℕ) (f : G → ℝ≥0)
    {p : ℝ} (hp : 0 < p) :
    gowers (r • μ) d p f = (r : ℝ≥0∞) ^ (((d : ℝ) + p) / ((2 : ℝ) ^ d * p)) *
      gowers μ d p f := by
  have hroot : 0 ≤ 1 / p := by positivity
  have hcube : 0 ≤ 1 / (2 : ℝ) ^ d := by positivity
  have hR : autocorrelation (r • μ) d f = fun h => (r : ℝ≥0∞) * autocorrelation μ d f h := by
    funext h
    rw [autocorrelation, lintegral_smul_measure]
    rfl
  unfold gowers
  rw [hR, cubeMeasure_smul, lp_const_mul _ _ _ ENNReal.coe_ne_top hp]
  unfold lp
  rw [lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
    ENNReal.mul_rpow_of_nonneg _ _ hroot, ENNReal.mul_rpow_of_nonneg _ _ hcube,
    ← ENNReal.rpow_mul]
  rw [← mul_assoc, ← ENNReal.rpow_natCast_mul, mul_comm ((r : ℝ≥0∞) ^ (1 / (2 : ℝ) ^ d)),
    ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
  congr 2
  field_simp

end LpGowers
