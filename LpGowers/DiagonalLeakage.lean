module

public import LpGowers.DegreeProofs
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic

/-! # The Cauchy–Schwarz estimate for diagonal leakage

Following §6 of Kovač–Rogers, change from adjacent cube edges to opposite
vertices `x,y` and apply Cauchy–Schwarz with the weight `f x * f y`.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]

/-- Nonnegative autoconvolution, with values in the extended nonnegative reals. -/
def selfConvolution (f : G → ℝ≥0∞) (t : G) : ℝ≥0∞ := ∫⁻ u, f u * f (t-u) ∂μ

omit [μ.IsAddLeftInvariant] in
private theorem meas_selfConvolution {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (selfConvolution μ f) := by
  apply Measurable.lintegral_prod_right
  exact (hf.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))

/-- The two-variable Cauchy–Schwarz step after the paper's shear of cube coordinates. -/
theorem diagonal_pair_estimate {f : G → ℝ≥0∞} (hf : Measurable f)
    {A : Set G} (hA : MeasurableSet A) :
    (∫⁻ z : G × G, A.indicator 1 (z.2-z.1) * (f z.1*f z.2) *
      selfConvolution μ f (z.1+z.2) ∂μ.prod μ) ≤
    (∫⁻ s in A, ∫⁻ x, f x*f (x+s) ∂μ ∂μ) ^ (1/2:ℝ) *
      (∫⁻ t, (selfConvolution μ f t)^3 ∂μ) ^ (1/2:ℝ) := by
  classical
  let C := selfConvolution μ f
  have hC : Measurable C := meas_selfConvolution μ hf
  let I : G → ℝ≥0∞ := A.indicator 1
  have hI : Measurable I := measurable_const.indicator hA
  let W (z : G × G) := f z.1 * f z.2
  let U (z : G × G) := I (z.2-z.1) * W z
  let V (z : G × G) := W z * C (z.1+z.2)^2
  have hW : Measurable W := (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hU : Measurable U := (hI.comp (measurable_snd.sub measurable_fst)).mul hW
  have hV : Measurable V := hW.mul ((hC.comp (measurable_fst.add measurable_snd)).pow_const 2)
  have hhalf : (0:ℝ) ≤ 1/2 := by norm_num
  have hpoint (z : G × G) : I (z.2-z.1) * W z * C (z.1+z.2) = U z ^ (1/2:ℝ) * V z ^ (1/2:ℝ) := by
    dsimp only [U,V]
    rw [ENNReal.mul_rpow_of_nonneg (I _) (W z) hhalf,
      ENNReal.mul_rpow_of_nonneg (W z) (C _ ^ 2) hhalf,
      ← ENNReal.rpow_natCast (C _) 2, ← ENNReal.rpow_mul]
    have hw := ENNReal.rpow_add_of_nonneg (x := W z) _ _ hhalf hhalf
    norm_num at hw ⊢
    by_cases hz : z.2-z.1 ∈ A
    · simp only [I, Set.indicator_of_mem hz, Pi.one_apply, one_mul, ENNReal.one_rpow]
      rw [← mul_assoc, ← hw]
    · simp [I, hz, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<2⁻¹)]
  have hmassU : ∫⁻ z, U z ∂μ.prod μ = ∫⁻ s in A, ∫⁻ x, f x * f (x+s) ∂μ ∂μ := by
    rw [lintegral_prod _ hU.aemeasurable]
    calc
      _ = ∫⁻ x, ∫⁻ s, I s * (f x * f (x+s)) ∂μ ∂μ := by
        apply lintegral_congr; intro x
        rw [← lintegral_add_left_eq_self (fun y => U (x,y)) x]
        simp [U, W]
      _ = ∫⁻ s, ∫⁻ x, I s * (f x * f (x+s)) ∂μ ∂μ := by
        apply lintegral_lintegral_swap
        exact ((hI.comp measurable_snd).mul ((hf.comp measurable_fst).mul
          (hf.comp (measurable_fst.add measurable_snd)))).aemeasurable
      _ = _ := by
        rw [← lintegral_indicator hA]
        apply lintegral_congr; intro s
        rw [lintegral_const_mul (μ := μ) (f := fun x => f x * f (x+s)) _
          (hf.mul (hf.comp (measurable_id.add measurable_const)))]
        by_cases hs : s ∈ A <;> simp [I, hs]
  have hmassV : ∫⁻ z, V z ∂μ.prod μ = ∫⁻ t, C t ^ 3 ∂μ := by
    rw [lintegral_prod _ hV.aemeasurable]
    calc
      _ = ∫⁻ x, ∫⁻ t, f x * f (t-x) * C t ^ 2 ∂μ ∂μ := by
        apply lintegral_congr; intro x
        rw [← lintegral_sub_right_eq_self (fun y => V (x,y)) x]
        simp [V,W]
      _ = ∫⁻ t, ∫⁻ x, f x * f (t-x) * C t ^ 2 ∂μ ∂μ := by
        apply lintegral_lintegral_swap
        exact (((hf.comp measurable_fst).mul (hf.comp (measurable_snd.sub measurable_fst))).mul
          ((hC.comp measurable_snd).pow_const 2)).aemeasurable
      _ = _ := by
        apply lintegral_congr; intro t
        rw [lintegral_mul_const (μ := μ) (f := fun x => f x * f (t-x)) _
          (hf.mul (hf.comp (measurable_const.sub measurable_id)))]
        change C t * C t ^ 2 = C t ^ 3
        ring
  calc
    _ = ∫⁻ z, U z ^ (1/2:ℝ) * V z ^ (1/2:ℝ) ∂μ.prod μ := lintegral_congr hpoint
    _ ≤ _ := by
      simpa only [hmassU, hmassV] using ENNReal.lintegral_mul_norm_pow_le (μ := μ.prod μ)
        hU.aemeasurable hV.aemeasurable hhalf hhalf (by norm_num)

/-- Rewriting a diagonally weighted cube integral in terms of opposite vertices.
This is the change of variables in the first part of the proof of Lemma 6.3. -/
theorem diagonal_opposite_vertices [SigmaFinite μ] {f : G → ℝ≥0} (hf : Measurable f)
    (I : G → ℝ≥0∞) (hI : Measurable I) :
    (∫⁻ h, I (h 0 + h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) =
      ∫⁻ z : G × G, I (z.2-z.1) * (liftNN f z.1 * liftNN f z.2) *
        selfConvolution μ (liftNN f) (z.1+z.2) ∂μ.prod μ := by
  let F := liftNN f
  have hF : Measurable F := measurable_coe_nnreal_ennreal.comp hf
  let C := selfConvolution μ F
  have hC : Measurable C := meas_selfConvolution μ hF
  let J (x h k : G) := I (h+k) * (F x * F (x+k) * (F (x+h) * F (x+h+k)))
  let L (x h y : G) := I (y-x) * (F x * F y) * (F (x+h) * F (y-h))
  let P (z : G × G) := I (z.2-z.1) * (F z.1 * F z.2) * C (z.1+z.2)
  have hP : Measurable P := by dsimp only [P]; fun_prop
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  let g (z : G × G) := I (z.1+z.2) * autocorrelation μ 2 f (e.symm z)
  have hg : Measurable g := (hI.comp (measurable_fst.add measurable_snd)).mul
    ((measurable_autocorrelation μ 2 hf).comp e.symm.measurable)
  have hstart : (∫⁻ h, I (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) =
      ∫⁻ z, g z ∂μ.prod μ := by
    rw [← he.lintegral_comp hg]
    apply lintegral_congr; intro h
    simp only [g, MeasurableEquiv.symm_apply_apply]
    rfl
  rw [hstart]
  change (∫⁻ z, g z ∂μ.prod μ) = ∫⁻ z, P z ∂μ.prod μ
  rw [lintegral_prod _ hP.aemeasurable]
  calc
    _ = ∫⁻ z : G × G, ∫⁻ x, J x z.1 z.2 ∂μ ∂μ.prod μ := by
      apply lintegral_congr; intro z
      dsimp only [J, g, autocorrelation]
      rw [lintegral_const_mul (μ := μ) (f := fun x => F x*F (x+z.2)*(F (x+z.1)*F (x+z.1+z.2))) _ (by fun_prop)]
      rfl
    _ = ∫⁻ x, ∫⁻ z : G × G, J x z.1 z.2 ∂μ.prod μ ∂μ := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      dsimp only [Function.uncurry, J]; fun_prop
    _ = ∫⁻ x, ∫⁻ h, ∫⁻ y, L x h y ∂μ ∂μ ∂μ := by
      apply lintegral_congr; intro x
      rw [lintegral_prod (fun z : G × G => J x z.1 z.2) (by dsimp only [J]; fun_prop)]
      apply lintegral_congr; intro h
      rw [← lintegral_add_left_eq_self (L x h) (x+h)]
      apply lintegral_congr; intro k
      dsimp only [J,L]; simp only [show x+h+k-x=h+k by abel, show x+h+k-h=x+k by abel]
      ac_rfl
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ h, L x h y ∂μ ∂μ ∂μ := by
      apply lintegral_congr; intro x
      apply lintegral_lintegral_swap; apply Measurable.aemeasurable
      dsimp only [Function.uncurry, L]; fun_prop
    _ = _ := by
      apply lintegral_congr; intro x
      apply lintegral_congr; intro y
      dsimp only [L,P]
      rw [lintegral_const_mul (μ := μ) (f := fun h => F (x+h)*F (y-h)) _ (by fun_prop)]
      congr 1
      dsimp only [C,selfConvolution]
      rw [← lintegral_add_left_eq_self (fun u => F u * F ((x+y)-u)) x]
      apply lintegral_congr; intro h
      rw [show (x+y)-(x+h)=y-h by abel]

/-- Inequality (6.9) in the proof of the diagonal leakage lemma, in mass
notation: the second square root is the square root of the cubic integral. -/
theorem diagonal_leakage_convolution [SigmaFinite μ] {f : G → ℝ≥0} (hf : Measurable f)
    {A : Set G} (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, ∫⁻ x, liftNN f x * liftNN f (x+s) ∂μ ∂μ) ^ (1/2:ℝ) *
      (∫⁻ t, (selfConvolution μ (liftNN f) t)^3 ∂μ) ^ (1/2:ℝ) := by
  rw [diagonal_opposite_vertices μ hf (A.indicator 1) (measurable_const.indicator hA)]
  exact diagonal_pair_estimate μ (measurable_coe_nnreal_ennreal.comp hf) hA

/-- The same bound (6.9) for functions measurable in the completion of Haar
measure. The reflected translates of a null exceptional set are null. -/
theorem diagonal_leakage_convolution_ae [SigmaFinite μ] [μ.IsNegInvariant]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A : Set G} (hA : MeasurableSet A) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, ∫⁻ x, liftNN f x * liftNN f (x+s) ∂μ ∂μ) ^ (1/2:ℝ) *
      (∫⁻ t, (selfConvolution μ (liftNN f) t)^3 ∂μ) ^ (1/2:ℝ) := by
  let f' := hf.mk f
  have h : liftNN f =ᵐ[μ] liftNN f' := hf.ae_eq_mk.fun_comp (fun v : ℝ≥0 => (v : ℝ≥0∞))
  have hcorr (s : G) : (∫⁻ x, liftNN f x * liftNN f (x+s) ∂μ) =
      ∫⁻ x, liftNN f' x * liftNN f' (x+s) ∂μ := by
    exact lintegral_congr_ae (h.mul ((measurePreserving_add_right μ s).quasiMeasurePreserving.ae_eq_comp h))
  have hconv (t : G) : selfConvolution μ (liftNN f) t = selfConvolution μ (liftNN f') t := by
    exact lintegral_congr_ae (h.mul ((Measure.measurePreserving_sub_left μ t).quasiMeasurePreserving.ae_eq_comp h))
  rw [autocorrelation_congr_ae μ hf.ae_eq_mk]
  simp_rw [hcorr, hconv]
  exact diagonal_leakage_convolution μ hf.measurable_mk hA

end LpGowers
