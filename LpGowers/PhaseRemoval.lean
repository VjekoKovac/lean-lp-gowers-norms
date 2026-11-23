module

public import LpGowers.DiagonalLeakage

/-! # Cubic phase-removal inequality

We expand the cube of a correlation integral and replace three base points
by one base point and two differences. Cauchy–Schwarz then compares the
cubic integrals of an autoconvolution and an autocorrelation, as in §6.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]

/-- Product of three translates, parametrized by their two differences. -/
def triplePattern (f : G → ℝ≥0∞) (x : G) (z : G × G) := f x * (f (x+z.1)*f (x+z.2))

/-- Correlation of two nonnegative functions. -/
def pairCorrelation (f g : G → ℝ≥0∞) (t : G) := ∫⁻ x, f x * g (x+t) ∂μ

omit [μ.IsAddLeftInvariant] in
private lemma meas_corr {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable (pairCorrelation μ f g) :=
  Measurable.lintegral_prod_right ((hf.comp measurable_snd).mul (hg.comp (measurable_snd.add measurable_fst)))

/-- Expanding the cube into three independent integrals, then moving the
second and third variables by the first variable. -/
private lemma cube_integral {a : G → ℝ≥0∞} (ha : Measurable a) :
    (∫⁻ x, a x ∂μ)^3 = ∫⁻ x, ∫⁻ z : G × G, triplePattern a x z ∂μ.prod μ ∂μ := by
  have hmove (x : G) : (∫⁻ z : G × G, triplePattern a x z ∂μ.prod μ) =
      a x * ((∫⁻ u, a u ∂μ) * ∫⁻ v, a v ∂μ) := by
    have h := ((measurePreserving_add_left μ x).prod (measurePreserving_add_left μ x)).lintegral_comp
      (f := fun z : G × G => a z.1 * a z.2) ((ha.comp measurable_fst).mul (ha.comp measurable_snd))
    change (∫⁻ z : G × G, a (x+z.1)*a (x+z.2) ∂μ.prod μ) = _ at h
    unfold triplePattern
    rw [lintegral_const_mul (μ := μ.prod μ) (f := fun z : G × G => a (x+z.1)*a (x+z.2)) _ (by fun_prop),
      h, lintegral_prod_mul ha.aemeasurable ha.aemeasurable]
  simp_rw [hmove]
  rw [lintegral_mul_const _ ha]
  ring

/-- The joint cubic correlation of `f` and `g`, expressed as the inner product
of their three-point pattern counts. -/
theorem cubic_correlation_identity {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t, (pairCorrelation μ f g t)^3 ∂μ) =
      ∫⁻ z : G × G, (∫⁻ x, triplePattern f x z ∂μ) * (∫⁻ x, triplePattern g x z ∂μ) ∂μ.prod μ := by
  let J (x t : G) (z : G × G) := triplePattern f x z * triplePattern g (x+t) z
  have hslice (t : G) : (pairCorrelation μ f g t)^3 =
      ∫⁻ z : G × G, ∫⁻ x, J x t z ∂μ ∂μ.prod μ := by
    unfold pairCorrelation
    rw [cube_integral μ (a := fun x => f x * g (x+t)) (by fun_prop)]
    rw [lintegral_lintegral_swap (μ := μ) (ν := μ.prod μ)]
    · apply lintegral_congr; intro z
      apply lintegral_congr; intro x
      dsimp only [triplePattern, J]; rw [add_right_comm x z.1 t, add_right_comm x z.2 t]; ac_rfl
    · apply Measurable.aemeasurable
      change Measurable (fun z : G × (G × G) => triplePattern (fun x => f x * g (x+t)) z.1 z.2)
      dsimp only [triplePattern]; fun_prop
  simp_rw [hslice]
  rw [lintegral_lintegral_swap (μ := μ) (ν := μ.prod μ)]
  · apply lintegral_congr; intro z
    rw [lintegral_lintegral_swap (μ := μ) (ν := μ)]
    · have hinner (x : G) : (∫⁻ t, J x t z ∂μ) = triplePattern f x z * (∫⁻ t, triplePattern g t z ∂μ) := by
        dsimp only [J]
        rw [lintegral_const_mul (μ := μ) (f := fun t => triplePattern g (x+t) z) _ (by dsimp only [triplePattern]; fun_prop),
          lintegral_add_left_eq_self (fun t => triplePattern g t z)]
      simp_rw [hinner]
      exact lintegral_mul_const _ (by dsimp only [triplePattern]; fun_prop)
    · apply Measurable.aemeasurable; dsimp only [Function.uncurry, J, triplePattern]; fun_prop
  · apply Measurable.aemeasurable; apply Measurable.lintegral_prod_right
    dsimp only [Function.uncurry, J, triplePattern]; fun_prop

/-- Cauchy–Schwarz for the pair of three-point pattern counts, including
infinite cubic moments. -/
theorem cubic_correlation_le {f g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t, (pairCorrelation μ f g t)^3 ∂μ) ≤
      (∫⁻ t, (pairCorrelation μ f f t)^3 ∂μ) ^ (1/2:ℝ) *
      (∫⁻ t, (pairCorrelation μ g g t)^3 ∂μ) ^ (1/2:ℝ) := by
  let A (z : G × G) := ∫⁻ x, triplePattern f x z ∂μ
  let B (z : G × G) := ∫⁻ x, triplePattern g x z ∂μ
  have hA : Measurable A := by
    apply Measurable.lintegral_prod_right
    dsimp only [Function.uncurry,triplePattern]; fun_prop
  have hB : Measurable B := by
    apply Measurable.lintegral_prod_right
    dsimp only [Function.uncurry,triplePattern]; fun_prop
  rw [cubic_correlation_identity μ hf hg, cubic_correlation_identity μ hf hf,
    cubic_correlation_identity μ hg hg]
  have h2 : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  simpa only [Pi.mul_apply, ENNReal.rpow_two, pow_two, A, B] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod μ) h2 hA.aemeasurable hB.aemeasurable

/-- Equation (6.11) of arXiv:2609.08916v2. -/
theorem cubic_phase_removal [MeasurableNeg G] [μ.IsNegInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, (selfConvolution μ f t)^3 ∂μ) ≤ ∫⁻ t, (pairCorrelation μ f f t)^3 ∂μ := by
  let g (x : G) := f (-x)
  have hg : Measurable g := hf.comp measurable_neg
  have hfg (t : G) : pairCorrelation μ f g t = selfConvolution μ f (-t) := by
    apply lintegral_congr; intro x
    change f x * f (-(x+t)) = f x * f (-t-x)
    rw [show -(x+t)=-t-x by abel]
  have hgg (t : G) : pairCorrelation μ g g t = pairCorrelation μ f f (-t) := by
    unfold pairCorrelation
    rw [← lintegral_neg_eq_self (μ := μ) (fun x => g x * g (x+t))]
    apply lintegral_congr; intro x
    simp [g, add_comm]
  have h := cubic_correlation_le μ hf hg
  simp_rw [hfg, hgg] at h
  rw [lintegral_neg_eq_self (μ := μ) (fun t => (selfConvolution μ f t)^3),
    lintegral_neg_eq_self (μ := μ) (fun t => (pairCorrelation μ f f t)^3),
    ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h

omit [μ.IsAddLeftInvariant] in
/-- Identify the cubic Gowers expression with the cubic integral of the
ordinary one-dimensional autocorrelation. -/
theorem gowers_one_three_cube [SigmaFinite μ] {f : G → ℝ≥0} (hf : Measurable f) :
    (gowers μ 1 3 f)^3 = (∫⁻ t, (pairCorrelation μ (liftNN f) (liftNN f) t)^3 ∂μ) ^ (1/2:ℝ) := by
  let F := liftNN f
  have hm : Measurable F := measurable_coe_nnreal_ennreal.comp hf
  have hpi : (∫⁻ h, (autocorrelation μ 1 f h)^(3:ℝ) ∂cubeMeasure μ 1) =
      ∫⁻ t, (pairCorrelation μ F F t)^3 ∂μ := by
    have h := (measurePreserving_funUnique μ (Fin 1)).lintegral_comp
      (f := fun t => (pairCorrelation μ F F t)^3) ((meas_corr μ hm hm).pow_const 3)
    calc
      _ = ∫⁻ h, pairCorrelation μ F F (h 0)^3 ∂cubeMeasure μ 1 := by
        apply lintegral_congr; intro h
        exact ENNReal.rpow_natCast _ 3
      _ = _ := h
  rw [gowers, lp, hpi, ← ENNReal.rpow_natCast _ 3, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num [F]

/-- Equation (6.10), obtained by applying the cubic phase-removal inequality
to the weighted square estimate on opposite vertices. -/
theorem diagonal_leakage_gowers [MeasurableNeg G] [SigmaFinite μ] [μ.IsNegInvariant]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A : Set G} (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, pairCorrelation μ (liftNN f) (liftNN f) s ∂μ) ^ (1/2:ℝ) *
        (gowers μ 1 3 f)^3 := by
  let f' := hf.mk f
  have h : liftNN f =ᵐ[μ] liftNN f' := hf.ae_eq_mk.fun_comp (fun v : ℝ≥0 => (v : ℝ≥0∞))
  have hcorr (s : G) : pairCorrelation μ (liftNN f) (liftNN f) s = pairCorrelation μ (liftNN f') (liftNN f') s := by
    exact lintegral_congr_ae (h.mul ((measurePreserving_add_right μ s).quasiMeasurePreserving.ae_eq_comp h))
  have he : gowers μ 1 3 f = gowers μ 1 3 f' := by
    simp only [gowers, autocorrelation_congr_ae μ hf.ae_eq_mk 1]; rfl
  rw [autocorrelation_congr_ae μ hf.ae_eq_mk 2, he]
  simp_rw [hcorr]
  apply (diagonal_leakage_convolution μ hf.measurable_mk hA).trans
  rw [gowers_one_three_cube μ hf.measurable_mk]
  exact mul_le_mul_right (ENNReal.rpow_le_rpow
    (cubic_phase_removal μ (measurable_coe_nnreal_ennreal.comp hf.measurable_mk)) (by norm_num)) _

end LpGowers
