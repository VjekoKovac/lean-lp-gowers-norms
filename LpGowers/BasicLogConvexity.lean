module

public import LpGowers.LogConvexityProofs
public import LpGowers.SymmetricLowering

/-! Bennett–Tao log-convexity with constant one, obtained by the first
inequality chain in §6 of Kovač–Rogers. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

/-- The ordinary log-convexity estimate (1.4), before applying the strict-gap
argument. The extended nonnegative convention includes all measurable inputs. -/
theorem gowers_log_convex {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    ordinaryGowers μ d f ≤ ordinaryGowers μ (d - 1) f ^ logTheta d *
      ordinaryGowers μ (d + 1) f ^ (1 - logTheta d) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hd
  let D := (2 + j : ℕ)
  have hD : 2 ≤ (D : ℝ) := by exact_mod_cast hd
  have hden : 0 < 2 * (D : ℝ) - 1 := by linarith
  have hle : (D : ℝ) / (2 * D - 1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hrel : (1 : ℝ) * (1 / ((j : ℝ) + 1)) * (1 - (D : ℝ) / (2 * D - 1)) +
      (1 - 2) * (((D : ℝ) / (2 * D - 1)) / ((j : ℝ) + 2)) = 0 := by
    dsimp [D]
    push_cast
    ring_nf
    field_simp
    ring
  have hlow := degree_symmetric μ j (p := (D : ℝ) / (2 * D - 1)) (q := 1)
    (div_pos (by linarith : 0 < (D : ℝ)) hden) hle (by norm_num) hrel hf
  rw [show j + 2 = D by dsimp [D]; omega, show j + 1 = D - 1 by dsimp [D]; omega] at hlow
  have hθ : 0 ≤ logTheta D := div_nonneg (by positivity) (by linarith)
  exact (logConvexity_first_interpolation μ hf hd).trans
    (mul_le_mul_left (ENNReal.rpow_le_rpow hlow hθ) _)

end LpGowers
