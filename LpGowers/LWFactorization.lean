module

public import LpGowers.CoordinateMarginal
public import LpGowers.TensorTransfer
import Mathlib.Tactic

/-! # Factorization of near extremizers of Loomis–Whitney

For each pivot the lower-dimensional induction yields factors on all coordinates
except that pivot. Their one-coordinate marginals identify the local factors
with a common family on the original cube. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers

private theorem densityTensor_measurable {X : Type*} [MeasurableSpace X] {n : ℕ}
    {s : Fin n → X → ℝ≥0∞} (hs : ∀ j, Measurable (s j)) :
    Measurable (fun x : Fin n → X => ∏ i, s i (x i)) :=
  Finset.measurable_prod _ (fun i _ => (hs i).comp (measurable_pi_apply i))

private theorem glue_face_factors {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] {k : ℕ} {f : Fin (k+3) → (Fin (k+2) → X) → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hn : ∀ i, (∫⁻ x, f i x ∂cubeMeasure μ (k+2)) = 1)
    {e : ℝ≥0∞}
    (H : ∀ v : Fin (k+3), ∃ s : Fin (k+2) → X → ℝ≥0∞,
      (∀ j, Measurable (s j) ∧ (∫⁻ x, s j x ∂μ) = 1) ∧
      l1DensityError (cubeMeasure μ (k+2)) (f v) (fun y => ∏ j, s j (y j)) ≤ e ∧
      ∀ i, l1DensityError (cubeMeasure μ (k+1)) (lwContract μ k v f i)
        (fun y => ∏ m, s (i.succAbove m) (y m)) ≤ e) :
    ∃ r : Fin (k+3) → X → ℝ≥0∞,
      (∀ j, Measurable (r j) ∧ (∫⁻ x, r j x ∂μ) = 1) ∧
      ∀ v, l1DensityError (cubeMeasure μ (k+2)) (f v)
        (fun y => ∏ j, r (v.succAbove j) (y j)) ≤ e + (k+2 : ℕ) * e := by
  classical
  have existsFace (a : Fin (k+3)) : ∃ (p : Fin (k+3)) (j : Fin (k+2)), p.succAbove j = a := by
    obtain ⟨p, hp⟩ := exists_ne a
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hp.symm
    exact ⟨p,j,hj⟩
  choose p j hj using existsFace
  let r := fun a => coordinateMarginal μ (j a) (f (p a))
  have hr a : Measurable (r a) := coordinateMarginal_measurable μ _ (hf _)
  have hrn a : (∫⁻ x, r a x ∂μ) = 1 := (coordinateMarginal_mass μ _ (hf _)).trans (hn _)
  refine ⟨r, fun a => ⟨hr a, hrn a⟩, ?_⟩
  intro v
  obtain ⟨s,hs,h₀,h₁⟩ := H v
  have hc (b : Fin (k+2)) : l1DensityError μ (s b) (r (v.succAbove b)) ≤ e := by
    have h := local_marginal_consistency μ hf v s (fun i => (hs i).1) (fun i => (hs i).2)
      h₀ h₁ (p (v.succAbove b)) (j (v.succAbove b)) b (hj (v.succAbove b))
    simpa only [l1DensityError, add_comm, r] using h
  apply (l1DensityError_triangle _ (hf v) (densityTensor_measurable (fun i => (hs i).1))
    (densityTensor_measurable (fun i => hr (v.succAbove i)))).trans
  apply add_le_add h₀
  apply (l1_product_densities_le μ _ s (fun i => r (v.succAbove i)) (fun i => (hs i).1)
    (fun i => hr _) (fun i => (hs i).2) (fun i => hrn _)).trans
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hc i)

/-- At two coordinates each face is already a one-dimensional density. -/
private theorem two_face_factors {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {f : Fin 2 → (Fin 1 → X) → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (hn : ∀ i, (∫⁻ x, f i x ∂cubeMeasure μ 1) = 1) :
    ∃ r : Fin 2 → X → ℝ≥0∞,
      (∀ j, Measurable (r j) ∧ (∫⁻ x, r j x ∂μ) = 1) ∧
      ∀ v, l1DensityError (cubeMeasure μ 1) (f v)
        (fun y => ∏ j, r (v.succAbove j) (y j)) = 0 := by
  let r := fun i : Fin 2 => fun a : X => f (1-i) (fun _ => a)
  have hm (i) : Measurable (r i) := (hf _).comp (measurable_pi_iff.mpr (fun _ => measurable_id))
  have hN (i) : (∫⁻ a, r i a ∂μ) = 1 := by
    let e := MeasurableEquiv.funUnique (Fin 1) X
    have H := ((MeasurePreserving.symm e (measurePreserving_funUnique μ (Fin 1))).lintegral_comp (hf (1-i)))
    exact H.trans (hn _)
  refine ⟨r, fun i => ⟨hm i,hN i⟩, ?_⟩
  intro v
  have h (y : Fin 1 → X) : (∏ j, r (v.succAbove j) (y j)) = f v y := by
    rw [Fin.prod_univ_one]
    have hv : 1 - v.succAbove (0 : Fin 1) = v := by fin_cases v <;> decide
    have hy : (fun _ : Fin 1 => y 0) = y := funext fun i => congrArg y (Fin.eq_zero i).symm
    simp only [r, hv, hy]
  simp only [l1DensityError, h, tsub_self, add_zero, lintegral_zero]

/-- Lemma 5.2 of Kovač–Rogers for arbitrary normalized deletion-face
densities. The factors are probability densities, and a single family works
on every face. The threshold depends only on dimension and precision. -/
theorem lw_stability_ennreal (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (f : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞),
    (∀ i, Measurable (f i)) → (∀ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+1)) = 1) →
    ENNReal.ofReal (1-ε) ≤ ∫⁻ x, lwProduct k f x ∂cubeMeasure μ (k+2) →
    ∃ r : Fin (k+2) → X → ℝ≥0∞, (∀ j, Measurable (r j) ∧ (∫⁻ x, r j x ∂μ) = 1) ∧
      ∀ i, l1DensityError (cubeMeasure μ (k+1)) (f i)
        (fun y => ∏ j, r (i.succAbove j) (y j)) ≤ ENNReal.ofReal η := by
  induction k generalizing η with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro ε _ _ X _ μ _ f hf hn _
    obtain ⟨r,hr,he⟩ := two_face_factors μ hf hn
    exact ⟨r,hr,fun i => (he i).le.trans bot_le⟩
  | succ k ih =>
    let m : ℝ := k+2
    let τ := η / (m+1)
    let t := 1 / ((k:ℝ)+1)
    let b := τ / (4*m)
    let ζ := min τ (b ^ (t⁻¹))
    have hm : 0 < m := by dsimp [m]; positivity
    have hmcoe : ENNReal.ofReal m = (k+2 : ℕ) := by
      rw [show m = ((k+2:ℕ):ℝ) by simp [m], ENNReal.ofReal_natCast]
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have ht : 0 < t := by dsimp [t]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hζ : 0 < ζ := lt_min hτ (Real.rpow_pos_of_pos hb _)
    have hroot : ζ ^ t ≤ b := by
      apply (Real.rpow_le_rpow hζ.le (min_le_right _ _) ht.le).trans_eq
      exact Real.rpow_inv_rpow hb.le ht.ne'
    have he' : 2*m*(ζ^t) ≤ τ/2 := by
      apply (mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2*m)).trans_eq
      dsimp [b]; field_simp; ring
    have eBound : 2*(k+2:ℕ)*(ENNReal.ofReal ζ)^t ≤ ENNReal.ofReal (τ/2) := by
      have H := ENNReal.ofReal_le_ofReal he'
      simpa [ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg hζ.le ht.le, hm.le, hmcoe] using H
    obtain ⟨D,hD,HI⟩ := ih hζ
    let η₀ := min (τ/2) (D/2)
    have h₀ : 0 < η₀ := lt_min (half_pos hτ) (half_pos hD)
    obtain ⟨δ,hd,HC⟩ := lw_contraction_stability k h₀
    refine ⟨δ,hd,?_⟩
    intro ε he heδ X _ μ _ f hf hn hp
    have hpiv := HC ε he heδ μ f hf hn hp
    obtain ⟨r,hr,hface⟩ := glue_face_factors μ hf hn (e := ENNReal.ofReal τ) (by
      intro v
      let g := lwContract μ k v f
      obtain ⟨hgn,hmass,hcomp⟩ := hpiv v
      have hlt : η₀ < D := (min_le_right _ _).trans_lt (half_lt_self hD)
      obtain ⟨s,hs,hsface⟩ := HI η₀ h₀.le hlt μ g (fun i => (hgn i).1) (fun i => (hgn i).2) hmass
      let T := fun (i : Fin (k+2)) (y : Fin (k+1) → X) => ∏ j, s (i.succAbove j) (y j)
      have hTm i : Measurable (T i) := densityTensor_measurable (fun j => (hs (i.succAbove j)).1)
      have hTn i : (∫⁻ y, T i y ∂cubeMeasure μ (k+1)) = 1 := by
        simpa only [T, (fun j => (hs j).2), Finset.prod_const_one] using
          lintegral_pi_separated μ (k+1) (fun j => s (i.succAbove j)) (fun j => (hs _).1)
      have htrans := lw_product_transfer μ (fun i => (hgn i).1) hTm
        (fun i => (hgn i).2.le) (fun i => (hTn i).le) hsface
      have hTensor : lwProduct k T = fun x => ∏ i, s i (x i) := lwProduct_face_tensors k s
      rw [hTensor] at htrans
      refine ⟨s,hs,?_, fun i => (hsface i).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
      apply (l1DensityError_triangle _ (hf v) (lwProduct_measurable (fun i => (hgn i).1))
        (densityTensor_measurable (fun i => (hs i).1))).trans
      apply (add_le_add (hcomp.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
        (htrans.trans eBound)).trans_eq
      rw [← ENNReal.ofReal_add (half_pos hτ).le (half_pos hτ).le, add_halves])
    refine ⟨r,hr,fun v => (hface v).trans_eq ?_⟩
    have hc : τ + m*τ = η := by dsimp [τ]; field_simp; ring
    have H := congrArg ENNReal.ofReal hc
    simpa [ENNReal.ofReal_add hτ.le (mul_nonneg hm.le hτ.le), ENNReal.ofReal_mul hm.le, hmcoe] using H

/-- The finite-valued probability densities specified in Lemma 5.2. The
normalized inputs are the `(d−1)`st powers of the functions in that lemma. -/
theorem lw_stability (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (f : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞),
    (∀ i, Measurable (f i)) → (∀ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+1)) = 1) →
    ENNReal.ofReal (1-ε) ≤ ∫⁻ x, lwProduct k f x ∂cubeMeasure μ (k+2) →
    ∃ r : Fin (k+2) → X → ℝ≥0, (∀ j, Measurable (r j) ∧ (∫⁻ x, (r j x : ℝ≥0∞) ∂μ) = 1) ∧
      ∀ i, l1DensityError (cubeMeasure μ (k+1)) (f i)
        (fun y => ∏ j, (r (i.succAbove j) (y j) : ℝ≥0∞)) ≤ ENNReal.ofReal η := by
  obtain ⟨δ,hd,H⟩ := lw_stability_ennreal k hη
  refine ⟨δ,hd,?_⟩
  intro ε he heδ X _ μ _ f hf hn hp
  obtain ⟨s,hs,he⟩ := H ε he heδ μ f hf hn hp
  let r := fun j x => (s j x).toNNReal
  have hx (j) : ∀ᵐ x ∂μ, (r j x : ℝ≥0∞) = s j x := by
    filter_upwards [ae_lt_top (hs j).1 (by simp [(hs j).2])] with x h
    exact ENNReal.coe_toNNReal h.ne
  refine ⟨r,fun j => ⟨(hs j).1.ennreal_toNNReal, (lintegral_congr_ae (hx j)).trans (hs j).2⟩,?_⟩
  intro i
  apply le_trans _ (he i)
  apply le_of_eq
  apply lintegral_congr_ae
  have h (j : Fin (k+1)) : ∀ᵐ y ∂cubeMeasure μ (k+1),
      (r (i.succAbove j) (y j) : ℝ≥0∞) = s (i.succAbove j) (y j) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin (k+1) => μ) j).ae (hx (i.succAbove j))
  filter_upwards [ae_all_iff.mpr h] with y hy
  simp only [hy]

end LpGowers
