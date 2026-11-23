module

public import LpGowers.ExtendedHolder
public import LpGowers.LoomisWhitney
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Tactic

/-! # Stability under contraction of a Loomis–Whitney product

The contraction step in the inductive proof of Lemma 5.2, following Cook and
Dembo, Appendix A.2. Any coordinate can be used as the pivot, and the face
densities may be different. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LpGowers

/-- Normalized near-extremizers induce normalized marginals on any contracted
cube. Their product is again a near-extremizer, and it is close in `L¹` to the
original density on the face opposite the pivot. The threshold is independent
of the measure space, the input densities and the choice of pivot. -/
theorem lw_contraction_stability (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞),
    (∀ i, Measurable (f i)) → (∀ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+2)) = 1) →
    ENNReal.ofReal (1-ε) ≤ ∫⁻ x, lwProduct (k+1) f x ∂cubeMeasure μ (k+3) →
    ∀ v : Fin (k+3), let g := lwContract μ k v f
      (∀ j, Measurable (g j) ∧ (∫⁻ z, g j z ∂cubeMeasure μ (k+1)) = 1) ∧
      ENNReal.ofReal (1-η) ≤ ∫⁻ y, lwProduct k g y ∂cubeMeasure μ (k+2) ∧
      l1DensityError (cubeMeasure μ (k+2)) (f v) (lwProduct k g) ≤ ENNReal.ofReal η := by
  let r := 1 / ((k:ℝ)+2)
  let t := ((k:ℝ)+1) / ((k:ℝ)+2)
  let γ : Fin 2 → ℝ := ![r,t]
  have hγ (i) : 0 < γ i := by fin_cases i <;> dsimp [γ,r,t] <;> positivity
  have hs : ∑ i, γ i = 1 := by
    simp [Fin.sum_univ_two,γ,r,t]
    field_simp
    ring
  obtain ⟨δ, hd, H⟩ := holder_stability_ennreal γ hγ hs hη
  refine ⟨δ, hd, ?_⟩
  intro ε he heδ X _ μ _ f hf hn hnear v
  let g := lwContract μ k v f
  let B := lwProduct k g
  let ν := cubeMeasure μ (k+2)
  let U : Fin 2 → (Fin (k+2) → X) → ℝ≥0∞ := ![f v,B]
  have hg i : Measurable (g i) := lwContract_measurable μ v hf i
  have hgn i : (∫⁻ z, g i z ∂cubeMeasure μ (k+1)) = 1 :=
    (lwContract_mass μ v hf i).trans (hn _)
  have hBm : Measurable B := lwProduct_measurable hg
  have hBn : (∫⁻ y, B y ∂ν) ≤ 1 := by
    apply (functionalLoomisWhitney μ k g hg).trans
    simp [hgn]
  have hm i : AEMeasurable (U i) ν := by
    fin_cases i
    · exact (hf v).aemeasurable
    · exact hBm.aemeasurable
  have hN i : (∫⁻ y, U i y ∂ν) ≤ 1 := by
    fin_cases i
    · exact (hn v).le
    · exact hBn
  have hP : ENNReal.ofReal (1-ε) ≤ ∫⁻ y, ∏ i, (U i y)^(γ i) ∂ν := by
    apply hnear.trans
    simpa [Fin.prod_univ_two, γ, U, r, t, g, B, ν] using lw_product_contraction μ k v f hf
  have hD : l1DensityError ν (f v) B ≤ ENNReal.ofReal η :=
    (H ε he heδ ν U hm hN hP 0).2 1
  refine ⟨fun i => ⟨hg i, hgn i⟩, ?_, hD⟩
  have hdiff : (∫⁻ y, f v y ∂ν) - (∫⁻ y, B y ∂ν) ≤ ENNReal.ofReal η :=
    (lintegral_sub_le B (f v) hBm).trans
      ((lintegral_mono (fun y => le_add_right (le_refl (f v y - B y)))).trans hD)
  have hnν : (∫⁻ y, f v y ∂ν) = 1 := hn v
  rw [hnν] at hdiff
  rw [ENNReal.ofReal_sub _ hη.le, ENNReal.ofReal_one, tsub_le_iff_right]
  simpa [add_comm] using tsub_le_iff_right.mp hdiff

end LpGowers
