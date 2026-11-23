module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic

/-! The equality case of the three-moment lemma of §6. We use the equality
case in Mathlib's integral Hölder inequality. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LpGowers

/-- If three distinct positive moments of a nonnegative measurable function
are all one, its values are zero or one almost everywhere. -/
theorem three_moments_exact {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hA : (∫⁻ x, F x ^ a ∂μ) = 1) (hB : (∫⁻ x, F x ^ b ∂μ) = 1)
    (hC : (∫⁻ x, F x ^ c ∂μ) = 1) :
    ∀ᵐ x ∂μ, F x = 0 ∨ F x = 1 := by
  let s := (c - b) / (c - a)
  let t := (b - a) / (c - a)
  have hac := hab.trans hbc
  have hs : 0 < s := div_pos (sub_pos.mpr hbc) (sub_pos.mpr hac)
  have ht : 0 < t := div_pos (sub_pos.mpr hab) (sub_pos.mpr hac)
  have hst : s + t = 1 := by dsimp [s, t]; field_simp; ring
  have hbal : a * s + c * t = b := by dsimp [s, t]; field_simp; ring
  let u := fun x => (F x) ^ (a * s)
  let v := fun x => (F x) ^ (c * t)
  have hu : AEMeasurable u μ := hF.pow_const _
  have hv : AEMeasurable v μ := hF.pow_const _
  have huu (x : X) : u x ^ (1 / s) = F x ^ a := by
    simp only [u, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hvv (x : X) : v x ^ (1 / t) = F x ^ c := by
    simp only [v, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  have huv (x : X) : (u * v) x = F x ^ b := by
    simp only [Pi.mul_apply, u, v, ← ENNReal.rpow_add_of_nonneg _ _
      (mul_nonneg ha.le hs.le) (mul_nonneg (ha.trans hac).le ht.le), hbal]
  have he := (ENNReal.lintegral_mul_eq_one_iff_of_lintegral_rpow_eq_one
      (Real.holderConjugate_one_div hs ht hst) hu hv (by simpa only [huu] using hA)
        (by simpa only [hvv] using hC)).mp (by simpa only [huv] using hB)
  have hfin := ae_lt_top' (hF.pow_const a) (hA.trans_ne (by simp))
  filter_upwards [he, hfin] with x h hfinx
  simp only [Pi.pow_apply, huu, hvv] at h
  by_cases hx : F x = 0
  · exact Or.inl hx
  right
  have hxt : F x ≠ ⊤ := by
    intro hxt
    simp [hxt, ENNReal.top_rpow_of_pos ha] at hfinx
  rcases lt_trichotomy (F x) 1 with hlt | heq | hgt
  · exact False.elim ((ENNReal.rpow_lt_rpow_of_exponent_gt
      (pos_iff_ne_zero.mpr hx) hlt hac).ne h.symm)
  · exact heq
  · exact False.elim ((ENNReal.rpow_lt_rpow_of_exponent_lt hgt hxt hac).ne h)

end LpGowers
