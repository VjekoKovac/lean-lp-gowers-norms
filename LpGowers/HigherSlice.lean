module

public import LpGowers.DegreeNear
public import LpGowers.MonotoneApproximation

/-! The two-free-coordinate slice in the proof of Theorem 1.1.
The sufficient quantitative selection condition follows by averaging
the normalized slice errors and the lower-order squared moment. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

private theorem cubeProduct_ne_top {G : Type*} [AddCommMonoid G] (k : ℕ) (f : G → ℝ≥0)
    (z : Fin k → G) (x : G) : cubeProduct k f z x ≠ ⊤ := by
  induction k generalizing x with
  | zero => exact ENNReal.coe_ne_top
  | succ k ih => exact ENNReal.mul_ne_top (ih _ _) (ih _ _)

/-- A product over the vertices indexed by the frozen increments. -/
def sliceInput {G : Type*} [AddCommMonoid G] (k : ℕ) (f : G → ℝ≥0) (z : Fin k → G) (x : G) :
    ℝ≥0 := (cubeProduct k f z x).toNNReal

theorem coe_sliceInput {G : Type*} [AddCommMonoid G] (k : ℕ) (f : G → ℝ≥0)
    (z : Fin k → G) (x : G) : (sliceInput k f z x : ℝ≥0∞) = cubeProduct k f z x :=
  ENNReal.coe_toNNReal (cubeProduct_ne_top _ _ _ _)

theorem sliceInput_aemeasurable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (k : ℕ) (z : Fin k → G) : AEMeasurable (sliceInput k f z) μ :=
  ENNReal.measurable_toNNReal.comp_aemeasurable (aemeasurable_cubeProduct_fixed μ hf k z)

/-- The three identities for the mass, first and second autocorrelations
of the same slice input. They hold pointwise in every increment. -/
theorem slice_autocorrelations {G : Type*} [AddCommMonoid G] [MeasurableSpace G]
    (μ : Measure G) (f : G → ℝ≥0) (k : ℕ) (z : Fin k → G) (u v : G) :
    let g := sliceInput k f z
    (∫⁻ x, (g x : ℝ≥0∞) ∂μ) = autocorrelation μ k f z ∧
    autocorrelation μ 1 g (fun _ => u) = autocorrelation μ (k+1) f (Fin.cons u z) ∧
    autocorrelation μ 2 g ![u,v] = autocorrelation μ (k+2) f (Fin.cons u (Fin.cons v z)) := by
  dsimp only
  refine ⟨lintegral_congr (coe_sliceInput _ _ _), ?_, ?_⟩
  · apply lintegral_congr; intro x
    simp [cubeProduct, coe_sliceInput]
  · apply lintegral_congr; intro x
    simp [cubeProduct, coe_sliceInput, Fin.tail]

private def consEquiv (G : Type*) [MeasurableSpace G] (k : ℕ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => G) 0).symm

private theorem cons_apply {G : Type*} [MeasurableSpace G] (k : ℕ) (x : G) (z : Fin k → G) :
    consEquiv G k (x,z) = Fin.cons x z := Fin.insertNth_zero' _ _

/-- Tonelli after splitting off the first increment. -/
theorem lintegral_cons {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (k : ℕ) {F : (Fin (k+1) → G) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ h, F h ∂cubeMeasure μ (k+1)) = ∫⁻ z, ∫⁻ x, F (Fin.cons x z) ∂μ ∂cubeMeasure μ k := by
  let _ : SigmaFinite (cubeMeasure μ k) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => G) 0
  have he : MeasurePreserving e (cubeMeasure μ (k+1)) (μ.prod (cubeMeasure μ k)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  rw [← ((MeasurePreserving.symm e he).lintegral_comp hF), lintegral_prod_symm' (f := fun z => F (e.symm z)) (hF.comp e.symm.measurable)]
  apply lintegral_congr; intro z
  apply lintegral_congr; intro x
  exact congrArg F (cons_apply k x z)

/-- Tonelli in the order used to select the two-dimensional slice. -/
theorem lintegral_two_free {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (k : ℕ) {F : (Fin (k+2) → G) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ h, F h ∂cubeMeasure μ (k+2)) =
      ∫⁻ z, ∫⁻ v, ∫⁻ u, F (Fin.cons u (Fin.cons v z)) ∂μ ∂μ ∂cubeMeasure μ k := by
  rw [lintegral_cons μ (k+1) hF, lintegral_cons μ k]
  have h := Measurable.lintegral_prod_left' (hF.comp (consEquiv G (k+1)).measurable) (μ := μ)
  simpa only [Function.comp_apply, cons_apply] using h

/-- A good slice exists when the integral of the two normalized costs is
smaller than the mass of the candidate box. The two thresholds are independent. -/
theorem exists_good_slice {X : Type*} [MeasurableSpace X] (μ : Measure X) (D : Set X)
    {L M : X → ℝ≥0∞} {a b : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (hb : b ≠ 0) (hb' : b ≠ ⊤)
    (hL : Measurable L)
    (hbound : (∫⁻ z in D, L z ∂μ)/a + (∫⁻ z in D, M z ∂μ)/b < μ D)
    (hD : MeasurableSet D) : ∃ z ∈ D, L z < a ∧ M z < b := by
  by_contra! hn
  have hcost : ∀ᵐ z ∂μ.restrict D, 1 ≤ L z/a + M z/b := by
    filter_upwards [ae_restrict_mem hD] with z hz
    by_cases h : L z < a
    · have h₁ : b/b ≤ M z/b := by gcongr; exact hn z hz h
      rw [ENNReal.div_self hb hb'] at h₁
      exact h₁.trans le_add_self
    · have h₁ : a/a ≤ L z/a := by gcongr; exact le_of_not_gt h
      rw [ENNReal.div_self ha ha'] at h₁
      exact h₁.trans le_self_add
  have h := lintegral_mono_ae hcost
  rw [lintegral_const, one_mul, Measure.restrict_apply_univ,
    lintegral_add_left (hL.div_const a) _] at h
  simp only [div_eq_mul_inv, lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr ha),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hb)] at h hbound
  exact (not_lt_of_ge h) hbound

end LpGowers
