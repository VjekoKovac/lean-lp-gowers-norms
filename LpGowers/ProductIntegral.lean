module

public import LpGowers.Defs
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-! # Integration of tensor products

A finite product of nonnegative coordinate functions has integral equal
to the product of its integrals. The factors may have infinite integral.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace LpGowers

/-- Tonelli's product formula for separate nonnegative functions of each
coordinate of a finite product, allowing infinite integrals. -/
theorem lintegral_pi_separated {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] (n : ℕ) (f : Fin n → G → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → G, ∏ i, f i (x i) ∂cubeMeasure μ n) = ∏ i, ∫⁻ y, f i y ∂μ := by
  unfold cubeMeasure
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
      let m : Fin (n + 1) → Measure G := fun _ => μ
      have ht : Measurable (fun z : Fin n → G => ∏ i, f i.succ (z i)) := by fun_prop
      calc
        _ = ∫⁻ z : G × (Fin n → G), f 0 z.1 * ∏ i, f i.succ (z.2 i)
            ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
            rw [← ((measurePreserving_piFinSuccAbove m 0).symm).lintegral_comp_emb
              (MeasurableEquiv.measurableEmbedding _)]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
        _ = _ := by
          rw [lintegral_prod_mul (hf 0).aemeasurable ht.aemeasurable, ih _ (fun i => hf _),
            Fin.prod_univ_succ]

end LpGowers
