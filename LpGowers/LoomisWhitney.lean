module

public import LpGowers.Defs
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # A functional Loomis–Whitney inequality

We integrate first in the initial coordinate, apply the finite-product Hölder
inequality there, and use two-factor Hölder on the remaining coordinates.
The input functions are nonnegative and may have infinite integral.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LpGowers

variable {X : Type*} [MeasurableSpace X]

/-- The vector obtained by omitting coordinate `i`, in increasing order. -/
@[expose] def deleteCoord {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → X) : Fin n → X :=
  fun j => x (i.succAbove j)

private lemma measurable_delete {n : ℕ} (i : Fin (n + 1)) :
    Measurable (deleteCoord (X := X) i) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply (i.succAbove j))

omit [MeasurableSpace X] in
private lemma delete_zero {n : ℕ} (a : X) (x : Fin n → X) :
    deleteCoord (0 : Fin (n+1)) (Fin.cons a x) = x := by
  funext j; simp [deleteCoord]

omit [MeasurableSpace X] in
private lemma delete_insert {n : ℕ} (v : Fin (n+2)) (j : Fin (n+1)) (a : X) (y : Fin (n+1) → X) :
    deleteCoord (v.succAbove j) (v.insertNth a y) =
      (j.predAbove v).insertNth a (deleteCoord j y) := by
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp [deleteCoord, Fin.succAbove_succAbove_predAbove]
  · funext z
    simp [Fin.removeNth, deleteCoord, Fin.succAbove_succAbove_succAbove_predAbove]

theorem measurable_insertCoord {n : ℕ} (v : Fin (n+1)) :
    Measurable (fun z : X × (Fin n → X) => v.insertNth (α := fun _ => X) z.1 z.2) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) v).symm.measurable

theorem lintegral_insertCoord (μ : Measure X) [SigmaFinite μ] {n : ℕ} (v : Fin (n+1))
    {F : (Fin (n+1) → X) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂cubeMeasure μ (n+1) =
      ∫⁻ y, ∫⁻ a, F (v.insertNth a y) ∂μ ∂cubeMeasure μ n := by
  let : SigmaFinite (cubeMeasure μ n) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) v
  have he : MeasurePreserving e (cubeMeasure μ (n+1)) (μ.prod (cubeMeasure μ n)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) v
  calc
    _ = ∫⁻ z, F (e.symm z) ∂(μ.prod (cubeMeasure μ n)) :=
      ((MeasurePreserving.symm e he).lintegral_comp hF).symm
    _ = _ := lintegral_prod_symm' _ (hF.comp e.symm.measurable)

theorem integral_cons (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    {F : (Fin (n+1) → X) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂cubeMeasure μ (n+1) =
      ∫⁻ y, ∫⁻ a, F (Fin.cons a y) ∂μ ∂cubeMeasure μ n := by
  simpa only [Fin.insertNth_zero'] using lintegral_insertCoord μ 0 hF

private lemma prod_meas {n : ℕ} {f : Fin (n+1) → (Fin n → X) → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (r : ℝ) :
    Measurable (fun x => ∏ i, f i (deleteCoord i x) ^ r) :=
  Finset.measurable_prod _ (fun i _ => ((hf i).comp (measurable_delete i)).pow_const r)

private lemma integral_one (μ : Measure X) [SigmaFinite μ]
    {f : (Fin 1 → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂cubeMeasure μ 1 = ∫⁻ a, f (fun _ => a) ∂μ := by
  let e := MeasurableEquiv.funUnique (Fin 1) X
  exact ((MeasurePreserving.symm e (measurePreserving_funUnique μ (Fin 1))).lintegral_comp hf).symm

private lemma lw_base (μ : Measure X) [SigmaFinite μ]
    (f : Fin 2 → (Fin 1 → X) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, (∏ i, f i (deleteCoord i x) ^ (1 / (1 : ℝ))) ∂cubeMeasure μ 2 ≤
      ∏ i, (∫⁻ y, f i y ∂cubeMeasure μ 1) ^ (1 / (1 : ℝ)) := by
  rw [integral_cons μ (prod_meas hf _)]
  simp only [one_div, inv_one, ENNReal.rpow_one]
  have hdel (a : X) (y : Fin 1 → X) :
      deleteCoord (1 : Fin 2) (Fin.cons a y) = fun _ => a := by
    funext j; have hj : j = 0 := Fin.eq_zero _; subst j; rfl
  have hbase (a : X) (y : Fin 1 → X) :
      (∏ i : Fin 2, f i (deleteCoord i (Fin.cons a y))) = f 0 y * f 1 (fun _ => a) := by
    rw [Fin.prod_univ_two, delete_zero, hdel]
  simp_rw [hbase]
  rw [Fin.prod_univ_two]
  have hm : Measurable (fun a : X => f 1 (fun _ : Fin 1 => a)) :=
    (hf 1).comp (measurable_pi_iff.mpr (fun _ => measurable_id))
  simp_rw [lintegral_const_mul _ hm]
  rw [lintegral_mul_const _ (hf 0), ← integral_one μ (hf 1)]

/-- The product of the `(d−1)`st roots of codimension-one densities. -/
@[expose] def lwProduct {X : Type*} (k : ℕ)
    (F : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞) (x : Fin (k+2) → X) : ℝ≥0∞ :=
  ∏ i, F i (deleteCoord i x) ^ (1 / ((k:ℝ)+1))

theorem lwProduct_measurable {X : Type*} [MeasurableSpace X] {k : ℕ}
    {F : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞} (hF : ∀ i, Measurable (F i)) :
    Measurable (lwProduct k F) := Finset.measurable_prod _ (fun i _ =>
      ((hF i).comp (measurable_delete i)).pow_const _)

/-- The deletion-face densities after integrating coordinate `v`. -/
@[expose] def lwContract (μ : Measure X) (k : ℕ) (v : Fin (k+3))
    (f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞) (i : Fin (k+2)) (z : Fin (k+1) → X) : ℝ≥0∞ :=
  ∫⁻ a, f (v.succAbove i) ((i.predAbove v).insertNth a z) ∂μ

theorem lwContract_measurable (μ : Measure X) [SigmaFinite μ] {k : ℕ} (v : Fin (k+3))
    {f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (i : Fin (k+2)) :
    Measurable (lwContract μ k v f i) :=
  Measurable.lintegral_prod_left' ((hf (v.succAbove i)).comp (measurable_insertCoord (i.predAbove v)))

theorem lwContract_mass (μ : Measure X) [SigmaFinite μ] {k : ℕ} (v : Fin (k+3))
    {f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (i : Fin (k+2)) :
    (∫⁻ z, lwContract μ k v f i z ∂cubeMeasure μ (k+1)) = ∫⁻ y, f (v.succAbove i) y ∂cubeMeasure μ (k+2) :=
  (lintegral_insertCoord μ (i.predAbove v) (hf (v.succAbove i))).symm

/-- Single-coordinate contraction in the induction for Loomis–Whitney. This
intermediate bound retains the two factors to which stability of Hölder applies. -/
theorem lw_product_contraction (μ : Measure X) [SigmaFinite μ] (k : ℕ) (v : Fin (k+3))
    (f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, lwProduct (k+1) f x ∂cubeMeasure μ (k+3)) ≤
      ∫⁻ y, f v y ^ (1 / ((k:ℝ)+2)) *
        lwProduct k (lwContract μ k v f) y ^ (((k:ℝ)+1) / ((k:ℝ)+2)) ∂cubeMeasure μ (k+2) := by
  let r : ℝ := 1 / ((k:ℝ)+2)
  let s : ℝ := 1 / ((k:ℝ)+1)
  let t : ℝ := ((k:ℝ)+1) / ((k:ℝ)+2)
  let g := lwContract μ k v f
  let B := lwProduct k g
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : (k : ℝ)+2 ≠ 0 := by positivity
  have hst : s * t = r := by dsimp [s,t,r]; field_simp
  have hprod (v : Fin (k+2) → ℝ≥0∞) :
      (∏ i, v i ^ s) ^ t = ∏ i, v i ^ r := by
    rw [← ENNReal.prod_rpow_of_nonneg ht]
    simp_rw [← ENNReal.rpow_mul, hst]
  have hsum : ∑ _i : Fin (k+2), r = 1 := by
    simp [r, Nat.cast_add, hden]
  have hinner (y : Fin (k+2) → X) :
      ∫⁻ a, (∏ i, f i (deleteCoord i (v.insertNth a y)) ^ r) ∂μ ≤
        f v y ^ r * B y ^ t := by
    have hsplit (a : X) : (∏ i, f i (deleteCoord i (v.insertNth a y)) ^ r) =
        f v y ^ r * ∏ i : Fin (k+2), f (v.succAbove i) ((i.predAbove v).insertNth a (deleteCoord i y)) ^ r := by
      rw [Fin.prod_univ_succAbove _ v]
      have hv : deleteCoord v (v.insertNth a y) = y := funext (fun j => by simp [deleteCoord])
      rw [hv]
      simp only [delete_insert]
    simp_rw [hsplit]
    let A (i : Fin (k+2)) (a : X) := f (v.succAbove i) ((i.predAbove v).insertNth a (deleteCoord i y))
    have hA (i) : Measurable (A i) :=
      (hf (v.succAbove i)).comp ((measurable_insertCoord (i.predAbove v)).comp (measurable_id.prodMk measurable_const))
    change (∫⁻ a, f v y ^ r * ∏ i, A i a ^ r ∂μ) ≤ f v y ^ r * B y ^ t
    rw [lintegral_const_mul _ (Finset.measurable_prod _ (fun i _ => (hA i).pow_const r))]
    apply mul_le_mul_right
    dsimp only [B, lwProduct]
    change _ ≤ (∏ i, g i (deleteCoord i y) ^ s) ^ t
    rw [hprod]
    exact ENNReal.lintegral_prod_norm_pow_le Finset.univ (fun i _ => (hA i).aemeasurable)
      hsum (fun _ _ => hr)
  have hcast : ((k+1 : ℕ) : ℝ)+1 = (k : ℝ)+2 := by push_cast; ring
  conv_lhs => unfold lwProduct; simp only [hcast]
  rw [lintegral_insertCoord μ v (prod_meas hf r)]
  exact lintegral_mono hinner

/-- Functional Loomis–Whitney on `k+2` copies of any sigma-finite measure
space. The factor indexed by `i` omits the `i`th coordinate. -/
theorem functionalLoomisWhitney (μ : Measure X) [SigmaFinite μ] (k : ℕ)
    (f : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, (∏ i, f i (deleteCoord i x) ^ (1 / ((k : ℝ)+1))) ∂cubeMeasure μ (k+2) ≤
      ∏ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+1)) ^ (1 / ((k : ℝ)+1)) := by
  induction k with
  | zero => simpa using lw_base μ f hf
  | succ k ih =>
    let r : ℝ := 1 / ((k : ℝ)+2)
    let s : ℝ := 1 / ((k : ℝ)+1)
    let t : ℝ := ((k : ℝ)+1) / ((k : ℝ)+2)
    have hcast : ((k+1 : ℕ) : ℝ)+1 = (k : ℝ)+2 := by push_cast; ring
    simp only [hcast]
    change (∫⁻ x, (∏ i, f i (deleteCoord i x) ^ r) ∂cubeMeasure μ (k+3)) ≤
      ∏ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+2)) ^ r
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hden : (k : ℝ)+2 ≠ 0 := by positivity
    have hprev : (k : ℝ)+1 ≠ 0 := by positivity
    have hrt : r + t = 1 := by dsimp [r,t]; field_simp; ring
    have hst : s * t = r := by dsimp [s,t,r]; field_simp
    let g := lwContract μ k 0 f
    have hg (i) : Measurable (g i) := lwContract_measurable μ 0 hf i
    let B := lwProduct k g
    have hB : Measurable B := lwProduct_measurable hg
    have hprod (v : Fin (k+2) → ℝ≥0∞) :
        (∏ i, v i ^ s) ^ t = ∏ i, v i ^ r := by
      rw [← ENNReal.prod_rpow_of_nonneg ht]
      simp_rw [← ENNReal.rpow_mul, hst]
    calc
      _ ≤ ∫⁻ y, f 0 y ^ r * B y ^ t ∂cubeMeasure μ (k+2) := by
        simpa only [B, g, lwProduct, r, t, hcast] using lw_product_contraction μ k 0 f hf
      _ ≤ (∫⁻ y, f 0 y ∂cubeMeasure μ (k+2)) ^ r *
          (∫⁻ y, B y ∂cubeMeasure μ (k+2)) ^ t :=
        ENNReal.lintegral_mul_norm_pow_le (hf 0).aemeasurable hB.aemeasurable hr ht hrt
      _ ≤ (∫⁻ y, f 0 y ∂cubeMeasure μ (k+2)) ^ r *
          (∏ i, (∫⁻ z, g i z ∂cubeMeasure μ (k+1)) ^ s) ^ t := by
        exact mul_le_mul_right (ENNReal.rpow_le_rpow (ih g hg) ht) _
      _ = _ := by
        rw [hprod, Fin.prod_univ_succ (fun i : Fin (k+3) => (∫⁻ y, f i y ∂cubeMeasure μ (k+2)) ^ r)]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        simpa only [Fin.succAbove_zero] using congrArg (fun z : ℝ≥0∞ => z ^ r) (lwContract_mass μ 0 hf i)

end LpGowers
