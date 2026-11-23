module

public import LpGowers.DegreeNear
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Transferring indicator approximations to a nearby set

This combines the first and second absolute moments of the indicator error
in the reduction to a box in §6. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal symmDiff
namespace LpGowers

/-- Absolute error between an extended density and the indicator of a set. -/
def indicatorError {X : Type*} (F : X → ℝ≥0∞) (A : Set X) (x : X) : ℝ≥0∞ :=
  (F x - A.indicator 1 x) + (A.indicator 1 x - F x)

private theorem add_sq_bound (a b : ℝ≥0∞) : (a+b)^2 ≤ 2*(a^2+b^2) := by
  by_cases ha : a=⊤
  · simp [ha]
  by_cases hb : b=⊤
  · simp [hb]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_pow,ENNReal.toReal_add ha hb,ENNReal.toReal_mul,
    ENNReal.toReal_ofNat,ENNReal.toReal_add (by finiteness : a^2 ≠ ⊤) (by finiteness : b^2 ≠ ⊤)]
  nlinarith [sq_nonneg (a.toReal-b.toReal)]

/-- If a density approximates the indicator of `S` in its first and second
moments, replacing `S` by a nearby `B` costs at most six times the common
error tolerance in the sum of those moments. -/
theorem indicator_error_transfer {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (hF : Measurable F) {S B : Set X}
    (hS : MeasurableSet S) (hB : MeasurableSet B) (hs : μ S ≠ ⊤) (hb : μ B ≠ ⊤)
    {κ : ℝ} (_hk : 0 ≤ κ) (hmass : |μ.real S-1| ≤ κ) (hdiff : μ.real (S ∆ B) ≤ κ)
    (h1 : (∫⁻ x, indicatorError F S x ∂μ) ≤ ENNReal.ofReal κ)
    (h2 : (∫⁻ x, (indicatorError F S x)^2 ∂μ) ≤ ENNReal.ofReal κ) :
    |μ.real B - 1| ≤ 2*κ ∧
    (∫⁻ x, indicatorError F B x + (indicatorError F B x)^2 ∂μ) ≤ ENNReal.ofReal (6*κ) := by
  classical
  let I : Set X → X → ℝ≥0∞ := fun A => A.indicator 1
  let T := I (S ∆ B)
  let E := indicatorError F S
  have hT : Measurable T := measurable_const.indicator (hS.symmDiff hB)
  have hE : Measurable E := (hF.sub (measurable_const.indicator hS)).add
    ((measurable_const.indicator hS).sub hF)
  have hmassT : (∫⁻ x, T x ∂μ) ≤ ENNReal.ofReal κ := by
    have hfin := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hs,hb⟩)
      ((measure_mono (Set.symmDiff_subset_union : S ∆ B ⊆ S ∪ B)).trans (measure_union_le _ _))
    have H := ENNReal.ofReal_le_ofReal hdiff
    simpa [T,I, lintegral_indicator_one (hS.symmDiff hB), Measure.real, ENNReal.ofReal_toReal hfin] using H
  have hT2 (x) : T x ^ 2 = T x := by by_cases h : x ∈ S ∆ B <;> simp [T,I,h]
  have ht (x) : indicatorError F B x ≤ E x + T x := by
    have ht : (F x - I B x) + (I B x - F x) ≤
      ((F x-I S x)+(I S x-F x)) + ((I S x-I B x)+(I B x-I S x)) := by
      calc
        _ ≤ _ := add_le_add (tsub_le_tsub_add_tsub (a := F x) (b := I S x) (c := I B x))
          (tsub_le_tsub_add_tsub (a := I B x) (b := I S x) (c := F x))
        _ = _ := by ac_rfl
    have hd : (I S x-I B x)+(I B x-I S x) = T x := by
      by_cases h : x ∈ S <;> by_cases h' : x ∈ B <;> simp [I,T,Set.mem_symmDiff,h,h']
    exact ht.trans_eq (congrArg (_ + ·) hd)
  have hr₁ : (∫⁻ x, indicatorError F B x ∂μ) ≤ ENNReal.ofReal κ + ENNReal.ofReal κ := by
    apply (lintegral_mono ht).trans
    rw [lintegral_add_left hE]
    exact add_le_add h1 hmassT
  have hr₂ : (∫⁻ x, (indicatorError F B x)^2 ∂μ) ≤ 2*(ENNReal.ofReal κ+ENNReal.ofReal κ) := by
    calc
      _ ≤ ∫⁻ x, 2*((E x)^2+T x) ∂μ := by
        apply lintegral_mono
        intro x
        simpa only [hT2] using (pow_le_pow_left' (ht x) 2).trans (add_sq_bound (E x) (T x))
      _ = _ := by
        rw [lintegral_const_mul (f := fun x => (E x)^2+T x) _ ((hE.pow_const (2:ℕ)).add hT), lintegral_add_left (f := fun x => (E x)^2) (hE.pow_const (2:ℕ))]
      _ ≤ _ := mul_le_mul_right (add_le_add h2 hmassT) _
  constructor
  · have hA := measureReal_sdiff_add_inter (μ := μ) (s := S) hB hs
    have hC := measureReal_sdiff_add_inter (μ := μ) (s := B) hS hb
    rw [Set.inter_comm B S] at hC
    rw [measureReal_symmDiff_eq hS hB hs hb] at hdiff
    apply abs_le.mpr
    have hbounds := abs_le.mp hmass
    constructor <;> linarith [measureReal_nonneg (μ := μ) (s := S \ B),measureReal_nonneg (μ := μ) (s := B \ S)]
  · have hB' : Measurable (indicatorError F B) := (hF.sub (measurable_const.indicator hB)).add
      ((measurable_const.indicator hB).sub hF)
    rw [lintegral_add_left hB', ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6),ENNReal.ofReal_ofNat]
    exact (add_le_add hr₁ hr₂).trans_eq (by ring)

end LpGowers
