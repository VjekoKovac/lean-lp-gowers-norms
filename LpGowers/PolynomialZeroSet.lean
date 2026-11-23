module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A nonzero real polynomial has Lebesgue-null zero set, by induction on
the number of variables. This gives unique polynomial coefficients from
values on a positive-measure set. -/
@[expose] public section
open MeasureTheory MeasureTheory.Measure Filter MvPolynomial
namespace LpGowers

theorem ae_mvPolynomial_eval_ne_zero (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ ∂volume, MvPolynomial.eval x p ≠ 0 := by
  classical
  induction n with
  | zero =>
    filter_upwards [] with x
    intro hx
    apply hp
    apply MvPolynomial.funext
    intro y
    simpa only [Subsingleton.elim y x, map_zero] using hx
  | succ n ih =>
    let q := finSuccEquiv ℝ n p
    have hq : q ≠ 0 := by simpa [q] using hp
    obtain ⟨j,hj⟩ : ∃ j, q.coeff j ≠ 0 := by
      by_contra! h
      exact hq (AddMonoidAlgebra.ext (Finsupp.ext (by simpa using h)))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    let S (z : ℝ × (Fin n → ℝ)) := eval (e.symm z) p ≠ 0
    have hS : MeasurableSet {z | S z} := by
      exact ((p.continuous_eval.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl)
    have h : ∀ᵐ x : Fin n → ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, S (y,x) := by
      filter_upwards [ih (q.coeff j) hj] with x hx
      have hn : q.map (eval x) ≠ 0 := by
        intro he
        apply hx
        simpa using congrArg (fun r : Polynomial ℝ => r.coeff j) he
      have hz := (Polynomial.finite_setOfPred_isRoot hn).measure_zero (volume : Measure ℝ)
      have hroots : ∀ᵐ y : ℝ ∂volume, ¬(q.map (eval x)).IsRoot y := by
        simpa [ae_iff] using hz
      filter_upwards [hroots] with y hy
      change eval ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (y,x)) p ≠ 0
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_zero',eval_eq_eval_mv_eval'] using! hy
    have hprod := (ae_prod_iff_ae_ae hS).2 ((ae_ae_comm hS).2 h)
    have hfin := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).quasiMeasurePreserving.ae hprod
    simpa [S,e] using hfin

end LpGowers
