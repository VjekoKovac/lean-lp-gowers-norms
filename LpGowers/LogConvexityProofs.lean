module

public import LpGowers.LogConvexity
public import LpGowers.DegreeProofs
public import LpGowers.Interpolation

/-! The two different interpolations in the proof of Theorem 1.1, §6.
Both inequalities below have constant one. The strict uniform improvement
requires the further rigidity and convolution arguments of that section. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace LpGowers

/-- First interpolation in §6, including infinite norm values. -/
theorem logConvexity_first_interpolation {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    ordinaryGowers μ d f ≤ gowers μ d ((d : ℝ) / (2 * d - 1)) f ^ logTheta d *
      ordinaryGowers μ (d + 1) f ^ (1 - logTheta d) := by
  have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hd₀ : 0 < (d : ℝ) := by linarith
  have h₁ : 0 < 2 * (d : ℝ) - 1 := by linarith
  have h₂ : 0 < 3 * (d : ℝ) - 2 := by linarith
  unfold ordinaryGowers logTheta
  rw [gowers_one_succ_eq_gowers_two μ hf d]
  apply gowers_interpolate μ d f (measurable_autocorrelation_of_aemeasurable μ d hf).aemeasurable
    (by norm_num) (div_pos hd₀ h₁) (by norm_num) (div_nonneg hd₀.le h₂.le)
    ((div_le_one h₂).mpr (by linarith))
  rw [div_div_div_comm]
  field_simp [hd₀.ne', h₁.ne', h₂.ne']
  linear_combination -(mul_inv_cancel₀ h₂.ne')

/-- Second interpolation in §6. It applies at degree d−1, so its upper
endpoint is 6(d−1)/(3d−4), strictly larger than two. -/
theorem logConvexity_second_interpolation {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    ordinaryGowers μ d f ≤ ordinaryGowers μ (d - 1) f ^ (1 / (3 * (d : ℝ) - 2)) *
      gowers μ (d - 1) (6 * ((d : ℝ) - 1) / (3 * d - 4)) f ^
        (1 - 1 / (3 * (d : ℝ) - 2)) := by
  have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have h₁ : 0 < 3 * (d : ℝ) - 2 := by linarith
  have h₂ : 0 < 3 * (d : ℝ) - 4 := by linarith
  have h₃ : 0 < (d : ℝ) - 1 := by linarith
  have he := gowers_one_succ_eq_gowers_two μ hf (d - 1)
  rw [show d - 1 + 1 = d by omega] at he
  unfold ordinaryGowers
  rw [he]
  apply gowers_interpolate μ (d - 1) f
    (measurable_autocorrelation_of_aemeasurable μ (d - 1) hf).aemeasurable
    (by norm_num) (by norm_num) (div_pos (mul_pos (by norm_num) h₃) h₂)
    (by positivity) ((div_le_one h₁).mpr (by linarith))
  field_simp
  ring

end LpGowers
