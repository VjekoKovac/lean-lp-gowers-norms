module

public import LpGowers.DiscreteFunctional
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite-support norm comparison on the lattice, with the exact cardinal
factor appearing in the one-dimensional sharpness estimate. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers.Discrete

theorem lp_le_card_mul_lp {m : ℕ} {A : Finset (Lattice m)} {f : Lattice m → ℝ≥0}
    (hf : ∀ x ∉ A, f x = 0) {r q : ℝ} (hr : 0<r) (hrq : r≤q) :
    lp Measure.count r (liftNN f) ≤ (A.card : ℝ≥0∞) ^ (1/r-1/q) * lp Measure.count q (liftNN f) := by
  let μ := (Measure.count : Measure (Lattice m)).restrict (A:Set (Lattice m))
  have hal (s : ℝ) (hs : 0<s) : eLpNorm' (fun x => (f x : ℝ)) s μ = lp Measure.count s (liftNN f) := by
    rw [eLpNorm'_eq_lintegral_eNorm,lp]
    apply congrArg (· ^ (1/s))
    have he (x : Lattice m) : ‖(f x : ℝ)‖ₑ ^ s = liftNN f x ^ s := by simp [liftNN]
    simp_rw [he]
    change (∫⁻ x in (A:Set (Lattice m)), liftNN f x ^ s ∂Measure.count) = _
    rw [← lintegral_indicator A.measurableSet]
    apply lintegral_congr; intro x
    by_cases h : x∈A <;> simp [h, liftNN, ENNReal.zero_rpow_of_pos hs, hf]
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ := μ) hr hrq
    ((measurable_of_countable (fun x => (f x : ℝ))).aestronglyMeasurable)
  rwa [hal r hr, hal q (hr.trans_le hrq), mul_comm, show μ Set.univ = A.card by
    simp [μ, Measure.count_apply_finset]] at h

end LpGowers.Discrete
