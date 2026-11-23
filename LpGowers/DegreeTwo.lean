module

public import LpGowers.DegreeProofs
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Two-dimensional degree lowering at the Lebesgue endpoint

This is the case `p=2/3`, `q₁=q₂=1` of the argument of Sections 2 and 5.
The three Hölder factors use the joint density and its two square-root marginals.
-/

@[expose] public section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

private theorem ae_zero_of_first_marginal {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] {F : G × G → ℝ≥0∞} {v : G → ℝ≥0∞}
    (hF : Measurable F) (hv : Measurable v)
    (h1 : ∀ x, (∫⁻ y, F (x,y) ∂μ) = v x ^ (2 : ℕ)) :
    ∀ᵐ z ∂μ.prod μ, v z.1 = 0 → F z = 0 := by
  apply (ae_prod_iff_ae_ae ((measurableSet_eq_fun (hv.comp measurable_fst) measurable_const).imp
    (measurableSet_eq_fun hF measurable_const))).2
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : v x = 0
  · have h := (lintegral_eq_zero_iff (hF.comp (measurable_const.prodMk measurable_id))).mp
      (by simpa [hx] using h1 x)
    exact h.mono (fun y hy _ => hy)
  · exact Filter.Eventually.of_forall (fun _ hy => (hx hy).elim)

/-- The instance of adjoint Loomis–Whitney used at the `d=2` Lebesgue endpoint.
The two square-root marginals agree and may vanish. -/
theorem twoThirds_of_square_marginals {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] {F : G × G → ℝ≥0∞} {v : G → ℝ≥0∞}
    (hF : Measurable F) (hv : Measurable v)
    (h1 : ∀ x, (∫⁻ y, F (x,y) ∂μ) = v x ^ (2 : ℕ))
    (h2 : ∀ y, (∫⁻ x, F (x,y) ∂μ) = v y ^ (2 : ℕ)) :
    (∫⁻ z, (F z) ^ (2/3 : ℝ) ∂μ.prod μ) ≤ (∫⁻ x, v x ∂μ) ^ (4/3 : ℝ) := by
  let N := ∫⁻ x, v x ∂μ
  by_cases htop : N = ⊤
  · change _ ≤ N ^ (4/3 : ℝ)
    simp [htop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 4/3)]
  let A := fun z : G × G => F z * (v z.1)⁻¹
  let B := fun z : G × G => F z * (v z.2)⁻¹
  let C := fun z : G × G => v z.1 * v z.2
  have hA : Measurable A := hF.mul (hv.comp measurable_fst).inv
  have hB : Measurable B := hF.mul (hv.comp measurable_snd).inv
  have hC : Measurable C := (hv.comp measurable_fst).mul (hv.comp measurable_snd)
  have hbound (a : ℝ≥0∞) : a ^ (2:ℕ) * a⁻¹ ≤ a := by
    rw [pow_two, mul_assoc]
    calc
      _ ≤ a * 1 := mul_le_mul (le_refl a) a.mul_inv_le_one (bot_le) (bot_le)
      _ = _ := mul_one a
  have IA : (∫⁻ z, A z ∂μ.prod μ) ≤ N := by
    rw [lintegral_prod _ hA.aemeasurable]
    apply lintegral_mono
    intro x
    dsimp only [A]
    rw [lintegral_mul_const (f := fun y => F (x,y)) (v x)⁻¹ (hF.comp (measurable_const.prodMk measurable_id)), h1]
    exact hbound _
  have IB : (∫⁻ z, B z ∂μ.prod μ) ≤ N := by
    rw [lintegral_prod_symm' _ hB]
    apply lintegral_mono
    intro y
    dsimp only [B]
    rw [lintegral_mul_const (f := fun x => F (x,y)) (v y)⁻¹ (hF.comp (measurable_id.prodMk measurable_const)), h2]
    exact hbound _
  have IC : (∫⁻ z, C z ∂μ.prod μ) = N * N := lintegral_prod_mul hv.aemeasurable hv.aemeasurable
  have hz₁ := ae_zero_of_first_marginal μ hF hv h1
  have hz₂ : ∀ᵐ z ∂μ.prod μ, v z.2 = 0 → F z = 0 := by
    have hs := ae_zero_of_first_marginal μ (hF.comp measurable_swap) hv h2
    exact measurePreserving_swap.quasiMeasurePreserving.ae hs
  have hvtop := ae_lt_top hv htop
  have hft : ∀ᵐ z ∂μ.prod μ, v z.1 < ⊤ := quasiMeasurePreserving_fst.ae hvtop
  have hst : ∀ᵐ z ∂μ.prod μ, v z.2 < ⊤ := quasiMeasurePreserving_snd.ae hvtop
  have factorization : ∀ᵐ z ∂μ.prod μ, F z ^ (2/3 : ℝ) ≤
      A z ^ (1/3 : ℝ) * B z ^ (1/3 : ℝ) * C z ^ (1/3 : ℝ) := by
    filter_upwards [hz₁, hz₂, hft, hst] with z hz₁ hz₂ ht₁ ht₂
    by_cases hz : F z = 0
    · simp [hz, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2/3)]
    have hc₁ := ENNReal.inv_mul_cancel (fun he => hz (hz₁ he)) ht₁.ne
    have hc₂ := ENNReal.inv_mul_cancel (fun he => hz (hz₂ he)) ht₂.ne
    have hprod : A z * B z * C z = (F z) ^ (2 : ℕ) := by
      dsimp only [A,B,C]
      calc
        _ = (F z * F z) * ((v z.1)⁻¹ * v z.1) * ((v z.2)⁻¹ * v z.2) := by ac_rfl
        _ = _ := by rw [hc₁, hc₂, mul_one, mul_one, pow_two]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/3),
      ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/3), hprod,
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := μ.prod μ) (Finset.univ : Finset (Fin 3))
    (f := ![A,B,C]) (p := fun _ => (1/3 : ℝ))
    (fun i _ => by fin_cases i <;> simp [hA.aemeasurable, hB.aemeasurable, hC.aemeasurable])
    (by norm_num) (by intros; norm_num)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hHolder
  calc
    _ ≤ _ := lintegral_mono_ae factorization
    _ ≤ _ := hHolder
    _ ≤ N ^ (1/3 : ℝ) * N ^ (1/3 : ℝ) * (N * N) ^ (1/3 : ℝ) := by
      rw [IC]
      gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/3)]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num [N]

/-- Symmetric degree lowering from `d=2,p=2/3` to `d=1,q=1`.
This is the first scaling-critical case used in Section 3. -/
theorem degree_two_twoThirds {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ 2 (2/3) f ≤ gowers μ 1 1 f := by
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  let e₁ : (Fin 1 → G) ≃ᵐ G := MeasurableEquiv.funUnique (Fin 1) G
  let v := fun x => autocorrelation μ 1 f (e₁.symm x)
  let F := fun z => autocorrelation μ 2 f (e.symm z)
  have hv : Measurable v := (measurable_autocorrelation_of_aemeasurable μ 1 hf).comp e₁.symm.measurable
  have hF : Measurable F := (measurable_autocorrelation_of_aemeasurable μ 2 hf).comp e.symm.measurable
  have h1 (x : G) : (∫⁻ y, F (x,y) ∂μ) = v x ^ (2:ℕ) := by
    convert! autocorrelation_marginal μ hf 1 (1 : Fin 2) (e₁.symm x) using 1
  have h2 (y : G) : (∫⁻ x, F (x,y) ∂μ) = v y ^ (2:ℕ) := by
    convert! autocorrelation_marginal μ hf 1 (0 : Fin 2) (e₁.symm y) using 1
  have J := twoThirds_of_square_marginals μ hF hv h1 h2
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  have he₁ : MeasurePreserving e₁ (cubeMeasure μ 1) μ := measurePreserving_funUnique μ (Fin 1)
  change (∫⁻ z, (autocorrelation μ 2 f (e.symm z)) ^ (2/3 : ℝ) ∂μ.prod μ) ≤
    (∫⁻ x, autocorrelation μ 1 f (e₁.symm x) ∂μ) ^ (4/3 : ℝ) at J
  rw [(MeasurePreserving.symm e he).lintegral_comp_emb e.symm.measurableEmbedding
    (fun h => autocorrelation μ 2 f h ^ (2/3 : ℝ)),
    (MeasurePreserving.symm e₁ he₁).lintegral_comp
      (measurable_autocorrelation_of_aemeasurable μ 1 hf)] at J
  have H := ENNReal.rpow_le_rpow J (by norm_num : (0:ℝ) ≤ 3/8)
  norm_num [gowers, lp, ← ENNReal.rpow_mul] at H ⊢
  exact H

end LpGowers
