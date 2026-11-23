module

public import LpGowers.YoungHeatEquality
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! # Quantitative bounds for near-extremal Brascamp–Lieb heat flows

The initial integral deficit bounds the L¹ error of Gaussian smoothing at
every positive time. For bounded-support data, some time in each positive
window also controls the squared incompatibility of all the row scores.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter GeometricBrascampLieb
open scoped BigOperators Topology
namespace LpGowers

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)] [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}

/-- Integrated deviation between smoothing the geometric product and multiplying
the smoothed row densities is at most the original Brascamp–Lieb deficit.
The bound is uniform over all positive times and all integrable row inputs. -/
theorem heat_error_le_initial_deficit
    (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0≤f i y) {t : ℝ} (ht : 0<t) :
    let g := fun x => ∏ i, (f i (D.map i x))^D.weight i
    let h := fun x => ∏ i, (heatConvolution (f i) t (D.map i x))^D.weight i
    (∫ x, |h x-heatConvolution g t x|) ≤
      (∏ i, (∫ y, f i y)^D.weight i) - ∫ x, g x := by
  dsimp only
  let g := fun x => ∏ i, (f i (D.map i x))^D.weight i
  let u := fun i => heatConvolution (f i) t
  let h := fun x => ∏ i, (u i (D.map i x))^D.weight i
  have hgi : Integrable g := D.integrable_prod_of_integrable hf hf0
  have hui i : Integrable (u i) := heatConvolution_integrable (hf i) ht
  have hu0 i y : 0≤u i y := mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg (hf0 i) _ _)
  have hhi : Integrable h := D.integrable_prod_of_integrable hui hu0
  change (∫ x, |h x-heatConvolution g t x|) ≤ _
  have habs x : |h x-heatConvolution g t x| = h x-heatConvolution g t x :=
    abs_of_nonneg (sub_nonneg.mpr (heatConvolution_prod_le D hf hf0 ht x))
  simp_rw [habs]
  rw [integral_sub hhi (heatConvolution_integrable hgi ht), integral_heatConvolution hgi ht]
  apply sub_le_sub_right
  simpa only [u,integral_heatConvolution (hf _) ht] using D.integral_prod_le_integrable hui hu0

omit [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
/-- The pointwise score defect integrated in space is the time derivative of
the heat functional, whenever the upstream analytic bounds hold. -/
theorem heat_integral_hasDerivAt_score_defect (U : ∀ i, LogHeatFlow (F i))
    (H : D.HeatIntegrability U) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun r => ∫ x, D.heatProduct U r x)
      (∫ x, D.heatProduct U t x * (∑ i, D.weight i *
          ‖(U i).gradient t (D.map i x) - D.map i (D.score U t x)‖^2)) t := by
  obtain ⟨V,hV,hV0,b,hb,hdom⟩ := H.local_time_bound t ht
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV
    (Eventually.mono (isOpen_Ioi.mem_nhds ht) (fun r hr => (H.product_integrable r hr).aestronglyMeasurable))
    (H.product_integrable t ht) (H.time_integrable t ht).aestronglyMeasurable
    (Eventually.of_forall fun x r hr => hdom r hr x) hb
    (Eventually.of_forall fun x r hr => D.heatProduct_hasDerivAt U (hV0 hr) x)).2
  let B := stdOrthonormalBasis ℝ E
  have hi (i) : Integrable (fun x => inner ℝ (B i) (D.fluxDerivative U t x (B i))) :=
    (innerSL ℝ (B i)).integrable_comp ((H.fluxDerivative_integrable t ht).apply_continuousLinearMap (B i))
  have hz := integral_trace_derivative_eq_zero B (H.flux_integrable t ht) hi (D.flux_hasFDerivAt U ht)
  have htr : Integrable (fun x => LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap) := by
    simp_rw [LinearMap.trace_eq_sum_inner _ B, ContinuousLinearMap.coe_coe]
    exact integrable_finsetSum _ (fun i _ => hi i)
  have he (x : E) := D.timeRate_sub_divergence U t x
  simp_rw [Datum.score,D.defect_eq_sum_sq] at he
  have hi' := integral_congr_ae (μ := (volume : Measure E)) (Eventually.of_forall he)
  rw [integral_sub (H.time_integrable t ht) htr,hz,sub_zero] at hi'
  exact h.congr_deriv hi'

omit [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
/-- Integrability of the weighted score defect under the same analytic heat-flow bounds. -/
theorem integrable_score_defect (U : ∀ i, LogHeatFlow (F i)) (H : D.HeatIntegrability U)
    {t : ℝ} (ht : 0<t) : Integrable (fun x => D.heatProduct U t x * (∑ i, D.weight i *
        ‖(U i).gradient t (D.map i x) - D.map i (D.score U t x)‖^2)) := by
  let B := stdOrthonormalBasis ℝ E
  have htr : Integrable (fun x => LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap) := by
    simp_rw [LinearMap.trace_eq_sum_inner _ B, ContinuousLinearMap.coe_coe]
    exact integrable_finsetSum _ (fun i _ => (innerSL ℝ (B i)).integrable_comp
      ((H.fluxDerivative_integrable t ht).apply_continuousLinearMap (B i)))
  apply ((H.time_integrable t ht).sub htr).congr
  exact Eventually.of_forall fun x => by
    have he := D.timeRate_sub_divergence U t x
    simp_rw [Datum.score,D.defect_eq_sum_sq] at he
    exact he

/-- On each positive time window, bounded-support data admit a scale at which
the integral of the weighted squared score error is bounded by the initial
BL deficit divided by the length of the time window. -/
theorem exists_small_score_defect_of_bounded_support
    (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i y, 0≤f i y) (hmass : ∀ i, 0<∫ y,f i y)
    {R : ι→ℝ} (hsupport : ∀ i y, f i y≠0 → ‖y‖≤R i) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    let U := fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)
    let gap := (∏ i, (∫ y, f i y)^D.weight i) - ∫ y, ∏ i, (f i (D.map i y))^D.weight i
    ∃ t ∈ Ioo a b, (∫ x, D.heatProduct U t x * (∑ i, D.weight i *
      ‖(U i).gradient t (D.map i x) - D.map i (D.score U t x)‖^2)) ≤ gap/(b-a) := by
  let U := fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)
  let P t := ∫ x, D.heatProduct U t x
  let W t := ∫ x, D.heatProduct U t x * (∑ i, D.weight i *
    ‖(U i).gradient t (D.map i x) - D.map i (D.score U t x)‖^2)
  have hd {t : ℝ} (ht : 0<t) : HasDerivAt P (W t) t :=
    heat_integral_hasDerivAt_score_defect D U (D.convolution_heatIntegrability hf hf0 hmass hsupport) ht
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope P W hab (fun r hr =>
    (hd (ha.trans_le hr.1)).continuousAt.continuousWithinAt) (fun r hr => hd (ha.trans hr.1))
  refine ⟨t,ht,he.le.trans (div_le_div_of_nonneg_right (sub_le_sub ?_ ?_) (sub_pos.mpr hab).le)⟩
  · dsimp only [P,U]
    simp_rw [D.heatProduct_convolution_eq_prod hf hf0 hmass (ha.trans hab)]
    have h := D.integral_prod_le_integrable (fun i => heatConvolution_integrable (hf i) (ha.trans hab))
      (fun i y => (heatConvolution_pos (hf i) (hf0 i) (hmass i) (ha.trans hab) y).le)
    simpa only [integral_heatConvolution (hf _) (ha.trans hab)] using h
  · let g := fun x => ∏ i, (f i (D.map i x)) ^ D.weight i
    have hg := D.integrable_prod_of_integrable hf hf0
    have h := integral_mono (heatConvolution_integrable hg ha)
      ((D.convolution_heatIntegrability hf hf0 hmass hsupport).product_integrable a ha)
      (fun x => (heatConvolution_prod_le D hf hf0 ha x).trans_eq
        (D.heatProduct_convolution_eq_prod hf hf0 hmass ha x).symm)
    exact (integral_heatConvolution hg ha).symm.le.trans h

end LpGowers
