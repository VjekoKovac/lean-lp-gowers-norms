module

public import LpGowers.LogConvexityProofs
public import LpGowers.LebesgueProofs
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! The necessity observation immediately following Theorem 1.1. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Classical

namespace LpGowers

/-- Haar homogeneity determines the interpolation weight. -/
theorem logTheta_balance (d : ℕ) (hd : 2 ≤ d) :
    (((d : ℝ) + 1) / 2 ^ d) =
      (((d - 1 : ℕ) + 1 : ℝ) / 2 ^ (d - 1)) * logTheta d +
      (((d + 1 : ℕ) + 1 : ℝ) / 2 ^ (d + 1)) * (1 - logTheta d) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hd
  simp only [logTheta, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show 2 + j - 1 = j + 1 by omega, show 2 + j = j + 2 by omega]
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  ring_nf
  field_simp
  ring

/-- The indicator of every compact open subgroup defeats every proposed
improvement of the constant one, for every d ≥ 2. -/
theorem compactOpen_obstruction {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (H : AddSubgroup G) (hc : IsCompact (H : Set G)) (ho : IsOpen (H : Set G))
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    let f := (H : Set G).indicator (fun _ => (1 : ℝ≥0))
    ENNReal.ofReal (1 - ε) * ordinaryGowers μ (d - 1) f ^ logTheta d *
      ordinaryGowers μ (d + 1) f ^ (1 - logTheta d) < ordinaryGowers μ d f := by
  let M := μ (H : Set G)
  have hM : M ≠ 0 := ne_of_gt (ho.measure_pos μ ⟨0, H.zero_mem⟩)
  have hMt : M ≠ ⊤ := hc.measure_ne_top
  let γ := ((d : ℝ) + 1) / (2 : ℝ) ^ d
  have hpos : M ^ γ ≠ 0 := (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hM) (by dsimp [γ]; positivity)).ne'
  have hfin : M ^ γ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by dsimp [γ]; positivity) hMt
  have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < 3 * (d : ℝ) - 2 := by linarith
  have ht : 0 ≤ logTheta d := div_nonneg (by positivity) hden.le
  have ht' : 0 ≤ 1 - logTheta d := sub_nonneg.mpr ((div_le_one hden).mpr (by linarith))
  dsimp only
  simp only [ordinaryGowers, gowers_subgroup_indicator μ H ho.measurableSet _ (by norm_num : (0:ℝ)<1),
    mul_one, ← ENNReal.rpow_mul]
  rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by positivity) ht)
    (mul_nonneg (by positivity) ht'), ← logTheta_balance d hd]
  have he : ENNReal.ofReal (1 - ε) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  simpa only [mul_one, one_mul, mul_comm (M ^ γ)] using ENNReal.mul_lt_mul_right hpos hfin he

end LpGowers
