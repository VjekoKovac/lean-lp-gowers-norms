module

public import LpGowers.LWStability
public import LpGowers.ProductIntegral
import Mathlib.Tactic

/-! # One-coordinate marginals

Contractivity, preservation of probability mass, and consistency of iterated
marginals, used to identify common tensor factors in Lemma 5.2. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LpGowers

variable {X : Type*} [MeasurableSpace X]

/-- Keep the coordinate `v` and integrate out every other coordinate. -/
def coordinateMarginal (μ : Measure X) {n : ℕ} (v : Fin (n+1))
    (f : (Fin (n+1) → X) → ℝ≥0∞) (a : X) : ℝ≥0∞ :=
  ∫⁻ y, f (v.insertNth a y) ∂cubeMeasure μ n

theorem coordinateMarginal_measurable (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    (v : Fin (n+1)) {f : (Fin (n+1) → X) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (coordinateMarginal μ v f) := by
  let : SigmaFinite (cubeMeasure μ n) := by unfold cubeMeasure; infer_instance
  exact Measurable.lintegral_prod_right' (hf.comp (measurable_insertCoord v))

theorem coordinateMarginal_mass (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    (v : Fin (n+1)) {f : (Fin (n+1) → X) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, coordinateMarginal μ v f a ∂μ) = ∫⁻ x, f x ∂cubeMeasure μ (n+1) := by
  let : SigmaFinite (cubeMeasure μ n) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) v
  have he : MeasurePreserving e (cubeMeasure μ (n+1)) (μ.prod (cubeMeasure μ n)) :=
    measurePreserving_piFinSuccAbove _ v
  rw [← ((MeasurePreserving.symm e he).lintegral_comp hf), lintegral_prod]
  · rfl
  · exact (hf.comp e.symm.measurable).aemeasurable

theorem coordinateMarginal_contraction (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    (v : Fin (n+1)) {f g : (Fin (n+1) → X) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    l1DensityError μ (coordinateMarginal μ v f) (coordinateMarginal μ v g) ≤
      l1DensityError (cubeMeasure μ (n+1)) f g := by
  let D := fun x => (f x-g x)+(g x-f x)
  have hD : Measurable D := (hf.sub hg).add (hg.sub hf)
  change _ ≤ ∫⁻ x, D x ∂cubeMeasure μ (n+1)
  rw [← coordinateMarginal_mass μ v hD]
  unfold l1DensityError
  apply lintegral_mono
  intro a
  let ins := fun y : Fin n → X => v.insertNth (α := fun _ => X) a y
  have hm : Measurable ins := (measurable_insertCoord v).comp (measurable_const.prodMk measurable_id)
  have hfa := hf.comp hm
  have hga := hg.comp hm
  change _ ≤ ∫⁻ y, (f (ins y) - g (ins y)) + (g (ins y) - f (ins y)) ∂cubeMeasure μ n
  rw [lintegral_add_left (f := fun y => f (ins y) - g (ins y)) (hfa.sub hga)]
  exact add_le_add (lintegral_sub_le _ _ hga) (lintegral_sub_le _ _ hfa)

theorem coordinateMarginal_tensor (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    (v : Fin (n+1)) (r : Fin (n+1) → X → ℝ≥0∞) (hr : ∀ i, Measurable (r i))
    (hn : ∀ i, (∫⁻ a, r i a ∂μ) = 1) :
    coordinateMarginal μ v (fun x => ∏ i, r i (x i)) = r v := by
  funext a
  unfold coordinateMarginal
  simp_rw [Fin.prod_univ_succAbove (fun i => r i _) v, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  have hm : Measurable (fun y : Fin n → X => ∏ i, r (v.succAbove i) (y i)) :=
    Finset.measurable_prod _ (fun i _ => (hr _).comp (measurable_pi_apply i))
  rw [lintegral_const_mul _ hm, lintegral_pi_separated μ n _ (fun i => hr (v.succAbove i))]
  simp [hn]

omit [MeasurableSpace X] in
private theorem insert_twice {n : ℕ} (v : Fin (n+2)) (j : Fin (n+1)) (a b : X) (z : Fin n → X) :
    v.insertNth (α := fun _ => X) a (j.insertNth (α := fun _ => X) b z) =
      (v.succAbove j).insertNth (α := fun _ => X) b ((j.predAbove v).insertNth (α := fun _ => X) a z) := by
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp
  · apply Fin.eq_insertNth_iff.mpr
    constructor
    · simp [Fin.removeNth, Fin.succAbove_succAbove_predAbove]
    · funext m
      simp [Fin.removeNth, Fin.succAbove_succAbove_succAbove_predAbove]

/-- Integrating a coordinate out before taking a one-dimensional marginal
gives the corresponding one-dimensional marginal of the original function. -/
theorem coordinateMarginal_after_integrating (μ : Measure X) [SigmaFinite μ] {n : ℕ}
    (v : Fin (n+2)) (j : Fin (n+1)) {f : (Fin (n+2) → X) → ℝ≥0∞} (hf : Measurable f) :
    coordinateMarginal μ j (fun y => ∫⁻ a, f (v.insertNth a y) ∂μ) =
      coordinateMarginal μ (v.succAbove j) f := by
  funext b
  unfold coordinateMarginal
  have hm : Measurable (fun z : Fin (n+1) → X => f ((v.succAbove j).insertNth b z)) :=
    hf.comp ((measurable_insertCoord _).comp (measurable_const.prodMk measurable_id))
  apply Eq.trans _ (lintegral_insertCoord μ (j.predAbove v) hm).symm
  apply lintegral_congr
  intro z
  exact lintegral_congr fun a => congrArg f (insert_twice v j a b z)

/-- A global coordinate can be read on any face that contains it. If a pivot
face and all contracted neighboring faces have compatible tensor approximations,
every possible marginal for a given coordinate is close to the same factor. -/
theorem local_marginal_consistency (μ : Measure X) [SigmaFinite μ] {k : ℕ}
    {f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (v : Fin (k+3)) (s : Fin (k+2) → X → ℝ≥0∞) (hs : ∀ j, Measurable (s j))
    (hn : ∀ j, (∫⁻ x, s j x ∂μ) = 1) {e : ℝ≥0∞}
    (h₀ : l1DensityError (cubeMeasure μ (k+2)) (f v) (fun y => ∏ j, s j (y j)) ≤ e)
    (h₁ : ∀ i, l1DensityError (cubeMeasure μ (k+1)) (lwContract μ k v f i)
      (fun y => ∏ m, s (i.succAbove m) (y m)) ≤ e)
    (p : Fin (k+3)) (a j : Fin (k+2)) (ha : p.succAbove a = v.succAbove j) :
    l1DensityError μ (coordinateMarginal μ a (f p)) (s j) ≤ e := by
  by_cases he : p=v
  · subst p
    have hj := Fin.succAbove_right_injective ha
    subst a
    rw [← coordinateMarginal_tensor μ j s hs hn]
    exact (coordinateMarginal_contraction μ j (hf v)
      (Finset.measurable_prod _ (fun i _ => (hs i).comp (measurable_pi_apply i)))).trans h₀
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq he
    have hji : j ≠ i := by
      rintro rfl
      exact Fin.succAbove_ne _ _ ha
    obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hji
    have hidx : a = (i.predAbove v).succAbove m := Fin.succAbove_right_injective
      (ha.trans (Fin.succAbove_succAbove_succAbove_predAbove v i m).symm)
    subst a
    let g := lwContract μ k v f i
    have hg : coordinateMarginal μ m g =
        coordinateMarginal μ ((i.predAbove v).succAbove m) (f (v.succAbove i)) :=
      coordinateMarginal_after_integrating μ (i.predAbove v) m (hf _)
    rw [← hg, ← coordinateMarginal_tensor μ m (fun b => s (i.succAbove b))
      (fun b => hs _) (fun b => hn _)]
    exact (coordinateMarginal_contraction μ m (lwContract_measurable μ v hf i)
      (Finset.measurable_prod _ (fun b _ => (hs _).comp (measurable_pi_apply b)))).trans (h₁ i)

end LpGowers
