module

public import LpGowers.PhaseRemoval
public import LpGowers.LebesgueProofs
public import Mathlib.MeasureTheory.Group.Prod

/-! # The diagonal leakage lemma

The final estimate uses the `d=2` reverse adjoint inequality. Testing against
truncations of the square-root marginal keeps the argument valid when a norm
may be infinite, without dividing by an infinite quantity.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace LpGowers

private lemma test_slice {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {b q : X → ℝ≥0∞} (hb : Measurable b) (hq : Measurable q) :
    (∫⁻ x, b x*q x ∂μ) ≤ (∫⁻ x, (b x)^3 ∂μ) ^ (1/3:ℝ) *
      ((∫⁻ x, q x ∂μ) ^ (1/3:ℝ) * (∫⁻ x, (q x)^2 ∂μ) ^ (1/3:ℝ)) := by
  let A (x) := b x ^ (3:ℕ)
  let C (x) := q x ^ (2:ℕ)
  have hA : Measurable A := hb.pow_const 3
  have hC : Measurable C := hq.pow_const 2
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
    (f := ![A,q,C]) (p := fun _ => (1/3:ℝ))
    (fun i _ => by fin_cases i <;> simp [hA.aemeasurable, hq.aemeasurable,hC.aemeasurable])
    (by norm_num) (by intros; norm_num)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at h
  rw [← mul_assoc]
  apply le_trans _ h
  apply lintegral_mono; intro x
  dsimp only [A,C]
  rw [← ENNReal.rpow_natCast (b x) 3, ← ENNReal.rpow_natCast (q x) 2,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc,
    ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

private lemma capped_marginal {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {F : X × X → ℝ≥0∞} (hF : Measurable F) {v b : X → ℝ≥0∞}
    (hv : Measurable v) (hb : Measurable b) (hbv : b ≤ v)
    (h1 : ∀ x, (∫⁻ y, F (x,y) ∂μ) = v x ^ 2)
    (h2 : ∀ y, (∫⁻ x, F (x,y) ∂μ) = v y ^ 2)
    (hBfin : (∫⁻ x, (b x)^3 ∂μ) ≠ ⊤) :
    (∫⁻ x, (b x)^3 ∂μ) ≤ (∫⁻ x, v x ∂μ) * (∫⁻ z, (F z)^2 ∂μ.prod μ) ^ (1/2:ℝ) := by
  let B := ∫⁻ x, (b x)^3 ∂μ
  let E (y : X) := ∫⁻ x, F (x,y)^2 ∂μ
  have hE : Measurable E := Measurable.lintegral_prod_left' (hF.pow_const 2)
  have hEint : (∫⁻ y, E y ∂μ) = ∫⁻ z, (F z)^2 ∂μ.prod μ :=
    (lintegral_prod_symm' _ (hF.pow_const 2)).symm
  let V := ∫⁻ x, v x ∂μ
  let D := ∫⁻ y, E y ∂μ
  have hrel : B ≤ B^(1/3:ℝ) * (V^(2/3:ℝ)*D^(1/3:ℝ)) := by
    calc
      B ≤ ∫⁻ x, b x * (v x)^2 ∂μ := by
        apply lintegral_mono; intro x
        change (b x)^3 ≤ b x * (v x)^2
        rw [show b x ^ 3 = b x * b x ^ 2 by ring]
        exact mul_le_mul_right (pow_le_pow_left' (hbv x) _) _
      _ = ∫⁻ x, ∫⁻ y, b x * F (x,y) ∂μ ∂μ := by
        apply lintegral_congr; intro x
        rw [lintegral_const_mul (μ := μ) (f := fun y => F (x,y)) _ (by fun_prop), h1]
      _ = ∫⁻ y, ∫⁻ x, b x * F (x,y) ∂μ ∂μ := by
        apply lintegral_lintegral_swap; exact ((hb.comp measurable_fst).mul hF).aemeasurable
      _ ≤ ∫⁻ y, B^(1/3:ℝ) * (v y ^ (2/3:ℝ) * E y ^ (1/3:ℝ)) ∂μ := by
        apply lintegral_mono; intro y
        have h := test_slice μ hb (q := fun x => F (x,y)) (by fun_prop)
        rw [h2, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul] at h
        norm_num only [Nat.cast_ofNat, show (2:ℝ)*(1/3)=2/3 by norm_num] at h
        exact h
      _ ≤ _ := by
        rw [lintegral_const_mul (μ := μ) (f := fun y => v y^(2/3:ℝ)*E y^(1/3:ℝ)) _ (by fun_prop)]
        exact mul_le_mul_right (ENNReal.lintegral_mul_norm_pow_le hv.aemeasurable hE.aemeasurable
          (by norm_num) (by norm_num) (by norm_num)) _
  by_cases hBzero : B=0
  · change B ≤ _; simp [hBzero]
  have hpos : (0:ℝ) < 1/2 := by norm_num
  have hB0 := (ENNReal.rpow_eq_zero_iff_of_pos hpos).not.mpr hBzero
  have hBt := (ENNReal.rpow_lt_top_iff_of_pos hpos).mpr (lt_top_iff_ne_top.mpr hBfin)
  have h := ENNReal.rpow_le_rpow hrel (by norm_num : (0:ℝ) ≤ 3/2)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2), ← ENNReal.rpow_mul] at h
  norm_num at h
  have hcollapse : B ^ (3/2:ℝ) = B^(1/2:ℝ) * B := by
    calc
      _ = B^((1/2:ℝ)+1) := by norm_num
      _ = _ := by rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
  rw [hcollapse] at h
  rw [← hEint]
  exact (ENNReal.mul_le_mul_iff_right hB0 hBt.ne).mp h

/-- An endpoint-free version of the special two-dimensional reverse adjoint
inequality. No square-integrability or positivity assumptions are required. -/
theorem cubic_square_marginal {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {F : X × X → ℝ≥0∞} (hF : Measurable F) {v : X → ℝ≥0∞} (hv : Measurable v)
    (h1 : ∀ x, (∫⁻ y, F (x,y) ∂μ) = v x ^ 2)
    (h2 : ∀ y, (∫⁻ x, F (x,y) ∂μ) = v y ^ 2) :
    (∫⁻ x, (v x)^3 ∂μ) ≤ (∫⁻ x, v x ∂μ) * (∫⁻ z, (F z)^2 ∂μ.prod μ) ^ (1/2:ℝ) := by
  by_cases hinf : (∫⁻ x, v x ∂μ) = ⊤
  · by_cases hz : (∫⁻ z, (F z)^2 ∂μ.prod μ) = 0
    · have hFa := (lintegral_eq_zero_iff' (hF.pow_const 2).aemeasurable).mp hz
      have hFzero : F =ᵐ[μ.prod μ] 0 := by
        filter_upwards [hFa] with z hz
        simpa using hz
      have hvsq : (∫⁻ x, (v x)^2 ∂μ) = 0 := by
        simp_rw [← h1]
        rw [← lintegral_prod F hF.aemeasurable, lintegral_congr_ae hFzero]; simp
      have hvnull := (lintegral_eq_zero_iff' (hv.pow_const 2).aemeasurable).mp hvsq
      refine Eq.trans_le ?_ zero_le
      exact (lintegral_eq_zero_iff' (hv.pow_const 3).aemeasurable).mpr (by
        filter_upwards [hvnull] with x hx
        simpa using hx)
    · rw [hinf, ENNReal.top_mul ((ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : (0:ℝ)<1/2)).not.mpr hz)]
      exact le_top
  let b (n : ℕ) (x : X) := min (v x) (n : ℝ≥0∞)
  have hb (n) : Measurable (b n) := hv.min measurable_const
  have hbv (n) : b n ≤ v := fun x => min_le_left _ _
  have hbfin (n) : (∫⁻ x, (b n x)^3 ∂μ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (n:ℝ≥0∞)^2 * ∫⁻ x, v x ∂μ)
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hinf
    · rw [← lintegral_const_mul _ hv]
      apply lintegral_mono; intro x
      change (b n x)^3 ≤ (n:ℝ≥0∞)^2 * v x
      rw [pow_succ]
      exact mul_le_mul' (pow_le_pow_left' (min_le_right (v x) _) 2) (hbv n x)
  have hlim (x) : (v x)^3 = ⨆ n, (b n x)^3 := by
    have hbtop : (⨆ n, b n x) = v x := by
      change (⨆ n : ℕ, v x ⊓ (n : ℝ≥0∞)) = v x
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    simpa only [ENNReal.rpow_natCast, hbtop] using
      ENNReal.iSup_rpow_of_pos (by norm_num : 0 < ((3:ℕ):ℝ)) (fun n => b n x)
  simp_rw [hlim]
  rw [lintegral_iSup (fun n => (hb n).pow_const 3) (by
    intro i j hij x; apply pow_le_pow_left'; exact min_le_min_left _ (Nat.cast_le.mpr hij))]
  exact iSup_le (fun n => capped_marginal μ hF hv (hb n) (hbv n) h1 h2 (hbfin n))

/-- The final reverse degree-lowering estimate used in Lemma 6.3, valid
for all extended values. -/
theorem cubic_gowers_reverse {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ] {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    (gowers μ 1 3 f)^3 ≤ lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
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
  have J := cubic_square_marginal μ hF hv h1 h2
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  have he₁ : MeasurePreserving e₁ (cubeMeasure μ 1) μ := measurePreserving_funUnique μ (Fin 1)
  change (∫⁻ x, (autocorrelation μ 1 f (e₁.symm x))^3 ∂μ) ≤
    (∫⁻ x, autocorrelation μ 1 f (e₁.symm x) ∂μ) *
    (∫⁻ z, (autocorrelation μ 2 f (e.symm z))^2 ∂μ.prod μ)^(1/2:ℝ) at J
  rw [(MeasurePreserving.symm e he).lintegral_comp_emb e.symm.measurableEmbedding
      (fun h => (autocorrelation μ 2 f h)^2),
    (MeasurePreserving.symm e₁ he₁).lintegral_comp_emb e₁.symm.measurableEmbedding
      (fun h => (autocorrelation μ 1 f h)^3),
    (MeasurePreserving.symm e₁ he₁).lintegral_comp_emb e₁.symm.measurableEmbedding
      (autocorrelation μ 1 f)] at J
  have h := ENNReal.rpow_le_rpow J (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← gowers_one_one μ hf, ordinaryGowers, gowers_one_succ_eq_gowers_two μ hf 2]
  rw [← ENNReal.rpow_natCast (gowers μ 1 3 f) 3, ← ENNReal.rpow_natCast (gowers μ 2 2 f) 2]
  norm_num [gowers, lp, ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤1/2),
    ENNReal.rpow_two] at h ⊢
  rw [← ENNReal.rpow_natCast (_ ^ (1/6:ℝ)) 3, ← ENNReal.rpow_natCast (_ ^ (1/8:ℝ)) 2,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num
  exact h

/-- Lemma 6.3 of arXiv:2609.08916v2. The two-dimensional cube integral is
restricted to increments whose sum belongs to the given measurable set. -/
theorem diagonal_leakage {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A : Set G} (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, pairCorrelation μ (liftNN f) (liftNN f) s ∂μ) ^ (1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  rw [mul_assoc]
  exact (diagonal_leakage_gowers μ hf hA).trans (mul_le_mul_right (cubic_gowers_reverse μ hf) _)

/-- Completed-measurability form of Lemma 6.3. The diagonal sum carries a
null exceptional set back to a product-null set by translation invariance. -/
theorem diagonal_leakage_nullMeasurableSet {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] [SigmaFinite μ] {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {A : Set G} (hA : NullMeasurableSet A μ) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, pairCorrelation μ (liftNN f) (liftNN f) s ∂μ) ^ (1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  obtain ⟨B, _, hB, hBA⟩ := hA.exists_measurable_superset_ae_eq
  have hI : B.indicator (1 : G → ℝ≥0∞) =ᵐ[μ] A.indicator 1 := indicator_ae_eq_of_ae_eq_set hBA
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  have hsum : QuasiMeasurePreserving (fun h : Fin 2 → G => h 0 + h 1) (cubeMeasure μ 2) μ :=
    (quasiMeasurePreserving_add μ μ).comp he.quasiMeasurePreserving
  have heq := (hsum.ae_eq_comp hI).mul (Filter.EventuallyEq.rfl (f := autocorrelation μ 2 f))
  have h := diagonal_leakage μ hf hB
  rw [Measure.restrict_congr_set hBA] at h
  exact (lintegral_congr_ae heq).symm.le.trans h

end LpGowers
