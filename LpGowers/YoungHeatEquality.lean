module

public import LpGowers.YoungFrameRigidity
public import GeometricBrascampLieb.IntegrableInequality
public import GeometricBrascampLieb.ConvolutionMonotonicity
import Mathlib.Tactic

/-! # Gaussian smoothing of equality in geometric Brascamp–Lieb

Applying the integral inequality to Gaussian-damped translates gives a
pointwise comparison. For extremizing integrable inputs its two sides have
the same mass and are continuous, hence coincide at every positive time.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LpGowers
open GeometricBrascampLieb

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}

omit [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
private theorem prod_gaussianKernel (b : ℝ) (z : E) :
    (∏ i, (gaussianKernel b (D.map i z)) ^ D.weight i) = gaussianKernel b z := by
  simp only [gaussianKernel, ← Real.exp_mul, ← Real.exp_sum]
  congr 1
  rw [← D.sum_weight_norm_sq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [MeasurableSpace E] [BorelSpace E] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
private theorem prod_heatNormalization (t : ℝ) :
    (∏ i, (heatNormalization (E := F i) t) ^ D.weight i) = heatNormalization (E := E) t := by
  simp only [heatNormalization, ← Real.exp_mul, ← Real.exp_sum]
  congr 1
  rw [← D.dimension_identity]
  set c := Real.log (4 * Real.pi * t)
  calc
    _ = ∑ i, (D.weight i * (Module.finrank ℝ (F i) : ℝ)) * (-c/2) :=
      Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The product of regularizations dominates the regularization of the geometric product. -/
theorem heatConvolution_prod_le (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0 ≤ f i y)
    {t : ℝ} (ht : 0 < t) (x : E) :
    heatConvolution (fun y => ∏ i, (f i (D.map i y)) ^ D.weight i) t x ≤
      ∏ i, (heatConvolution (f i) t (D.map i x)) ^ D.weight i := by
  let b := (4*t)⁻¹
  let u (i) (y : F i) := f i y * gaussianKernel b (D.map i x - y)
  have hu (i) : Integrable (u i) :=
    gaussianConvolution_integrand_integrable (hf i) (by dsimp [b]; positivity) (D.map i x)
  have hu0 i y : 0 ≤ u i y := mul_nonneg (hf0 i y) (Real.exp_pos _).le
  have hleft (y : E) : (∏ i, (u i (D.map i y)) ^ D.weight i) =
      (∏ i, (f i (D.map i y)) ^ D.weight i) * gaussianKernel b (x-y) := by
    rw [← prod_gaussianKernel D b (x-y), ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_sub]
    exact Real.mul_rpow (hf0 _ _) (Real.exp_pos _).le
  have h := D.integral_prod_le_integrable hu hu0
  simp_rw [hleft] at h
  have huMass i : (∫ y, u i y) = gaussianConvolution b (f i) (D.map i x) := rfl
  simp_rw [huMass] at h
  calc
    _ ≤ heatNormalization (E := E) t * ∏ i, gaussianConvolution b (f i) (D.map i x) ^ D.weight i :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      rw [← prod_heatNormalization D, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.mul_rpow (Real.exp_pos _).le (gaussianConvolution_nonneg (hf0 i) b _)).symm

/-- Equality in geometric BL is preserved pointwise by normalized Euclidean heat flow. -/
theorem heatConvolution_prod_eq_of_extremal
    (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0 ≤ f i y)
    (hEq : (∫ y, ∏ i, (f i (D.map i y)) ^ D.weight i) = ∏ i, (∫ y, f i y) ^ D.weight i)
    {t : ℝ} (ht : 0 < t) :
    heatConvolution (fun y => ∏ i, (f i (D.map i y)) ^ D.weight i) t =
      fun x => ∏ i, (heatConvolution (f i) t (D.map i x)) ^ D.weight i := by
  let g := fun y => ∏ i, (f i (D.map i y)) ^ D.weight i
  let u i := heatConvolution (f i) t
  let h := fun x => ∏ i, (u i (D.map i x)) ^ D.weight i
  have hg : Integrable g := D.integrable_prod_of_integrable hf hf0
  have hu i : Integrable (u i) := heatConvolution_integrable (hf i) ht
  have hu0 i y : 0 ≤ u i y := mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg (hf0 i) _ _)
  have hh : Integrable h := D.integrable_prod_of_integrable hu hu0
  have hle x : heatConvolution g t x ≤ h x := heatConvolution_prod_le D hf hf0 ht x
  have hinter : (∫ x, h x) ≤ ∫ x, heatConvolution g t x := by
    rw [integral_heatConvolution hg ht]
    change _ ≤ ∫ x, ∏ i, (f i (D.map i x)) ^ D.weight i
    rw [hEq]
    simpa only [u,integral_heatConvolution (hf _) ht] using D.integral_prod_le_integrable hu hu0
  have hdiff := (hh.sub (heatConvolution_integrable hg ht))
  have hdiffint : (∫ x, h x - heatConvolution g t x) = 0 := by
    rw [integral_sub hh (heatConvolution_integrable hg ht),sub_eq_zero]
    exact hinter.antisymm (integral_mono (heatConvolution_integrable hg ht) hh hle)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (hle x)) hdiff).mp hdiffint
  refine Measure.eq_of_ae_eq (μ := volume) ?_ (heatConvolution_continuous hg ht) ?_
  · filter_upwards [hae] with x hx
    exact (sub_eq_zero.mp hx).symm
  · apply continuous_finsetProd
    intro i _
    exact (((heatConvolution_continuous (hf i) ht).comp (D.map i).continuous).rpow_const
      fun _ => Or.inr (D.weight_nonneg i))

/-- For integrable extremizing data of positive mass the pointwise heat defect
vanishes at every positive time. This assertion does not require bounded support. -/
theorem heat_defect_zero_of_extremal
    (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0 ≤ f i y) (hmass : ∀ i, 0 < ∫ y, f i y)
    (hEq : (∫ y, ∏ i, (f i (D.map i y)) ^ D.weight i) = ∏ i, (∫ y, f i y) ^ D.weight i)
    {t : ℝ} (ht : 0 < t) (x : E) :
    let U := fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)
    (∑ i, D.weight i * ‖(U i).gradient t (D.map i x)‖ ^ 2) = ‖D.score U t x‖ ^ 2 := by
  let U := fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)
  let g := fun y => ∏ i, (f i (D.map i y)) ^ D.weight i
  have hg : Integrable g := D.integrable_prod_of_integrable hf hf0
  have he {r : ℝ} (hr : 0 < r) : D.heatProduct U r = heatConvolution g r := by
    rw [heatConvolution_prod_eq_of_extremal D hf hf0 hEq hr]
    exact funext (D.heatProduct_convolution_eq_prod hf hf0 hmass hr)
  have hgrad : D.flux U t = heatConvolutionGradient g t := by
    funext y
    apply innerSL_inj (𝕜 := ℝ) |>.mp
    have hfirst := D.heatProduct_hasFDerivAt U ht y
    rw [he ht] at hfirst
    simpa only [GeometricBrascampLieb.Datum.flux, he ht, map_smul] using
      hfirst.unique (heatConvolution_hasFDerivAt hg ht y)
  have hsecond := D.flux_hasFDerivAt U ht x
  rw [hgrad] at hsecond
  have hH := hsecond.unique (heatConvolutionGradient_hasFDerivAt hg ht x)
  have hp : (fun s => heatConvolution g s x) =ᶠ[𝓝 t] (fun s => D.heatProduct U s x) :=
    (lt_mem_nhds ht).mono fun s hs => congrFun (he hs).symm x
  have hT := (D.heatProduct_hasDerivAt U ht x).congr_of_eventuallyEq hp
  have hr := hT.unique (heatConvolution_hasDerivAt hg ht x)
  have hz := D.timeRate_sub_divergence U t x
  rw [hH, hr, sub_self] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left (D.heatProduct_pos U t x).ne')

section Young

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- For an exact diagonal Young-frame extremizer the logarithmic gradient of every
positive-time regularization of its repeated input is affine. -/
theorem affine_heat_score_of_young_frame_extremal {s : ℝ} (hs : 1 < s) (u v : V → ℝ)
    (hu : Integrable u) (hv : Integrable v) (hu0 : ∀ y, 0 ≤ u y) (hv0 : ∀ y, 0 ≤ v y)
    (hum : 0 < ∫ y, u y) (hvm : 0 < ∫ y, v y)
    (hEq : let f : Fin 3 → V → ℝ := ![u,u,v]
      (∫ y : WithLp 2 (V × V), ∏ i, (f i (youngFrameMap V s i y)) ^ youngFrameWeight s i) =
        ∏ i, (∫ y, f i y) ^ youngFrameWeight s i)
    {t : ℝ} (ht : 0 < t) :
    let F := (convolutionLogHeatFlow hu hu0 hum).gradient t
    ∃ L : V →L[ℝ] V, ∀ x, F x = L x + F 0 := by
  let f : Fin 3 → V → ℝ := ![u,u,v]
  have hfi (i) : Integrable (f i) := by fin_cases i <;> first | exact hu | exact hv
  have hfn (i) : ∀ y, 0 ≤ f i y := by fin_cases i <;> first | exact hu0 | exact hv0
  have hfm (i) : 0 < ∫ y, f i y := by fin_cases i <;> first | exact hum | exact hvm
  let D : Datum (Fin 3) (WithLp 2 (V × V)) (fun _ => V) :=
    .ofNormSq (youngFrameMap V s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry V (zero_lt_one.trans hs))
      (youngFrameMap_resolution V (zero_lt_one.trans hs))
  let U := convolutionLogHeatFlow hu hu0 hum
  let W := convolutionLogHeatFlow hv hv0 hvm
  apply affine_of_youngFrame_defect_zero hs (U.gradient t) (W.gradient t)
    (continuous_iff_continuousAt.mpr fun x => (U.gradient_deriv t ht x).continuousAt)
  intro z
  have he (i : Fin 3) :
      (convolutionLogHeatFlow (hfi i) (hfn i) (hfm i)).gradient t (D.map i z) =
        youngFrameFields s (U.gradient t) (W.gradient t) z i := by fin_cases i <;> rfl
  have h := heat_defect_zero_of_extremal D hfi hfn hfm hEq ht z
  dsimp only at h
  simp only [Datum.score, Datum.synthesis, he] at h
  exact h

end Young

end LpGowers
