module

public import LpGowers.YoungOrbitDefs
public import LpGowers.YoungGaussianOrbit
public import LpGowers.YoungHeatContinuity
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! A near-maximal diagonal Young input can be moved continuously, by heat flow,
to any prescribed intermediate distance from the normalized Gaussian orbit. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter GeometricBrascampLieb Set
open scoped Topology ENNReal NNReal

namespace LpGowers

private theorem heatGaussianInput_mem (n : ℕ) (q : ℝ) (hq : 0<q) {t : ℝ} (ht : 0<t) :
    (heatGaussianInput n hq ht).toLp hq ∈ unitGaussianSet n q hq :=
  ⟨_, rootedHeatGaussian_isGaussian n hq ht, rfl⟩

private theorem root_distance_bound {n : ℕ} {q : ℝ} (hq : 1≤q) [Fact (1≤ENNReal.ofReal q)]
    (u v : YoungHilbert n → ℝ) (hu : Integrable u) (hv : Integrable v)
    (hu0 : ∀ x, 0≤u x) (hv0 : ∀ x, 0≤v x) (U V : YoungUnitInput n q)
    (hU : U.val=densityRoot q u) (hV : V.val=densityRoot q v) :
    dist (U.toLp (zero_lt_one.trans_le hq)) (V.toLp (zero_lt_one.trans_le hq)) ≤
      (∫ x, ‖u x-v x‖)^(1/q) := by
  have hq0 := zero_lt_one.trans_le hq
  have h := densityRoot_distance hq hu hv hu0 hv0
  rw [← hU,← hV,← YoungUnitInput.edist_toLp U V hq0] at h
  have he := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.mpr hq0).le ENNReal.ofReal_ne_top) h
  simpa only [edist_dist,ENNReal.toReal_ofReal dist_nonneg,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))] using he

private theorem continuous_root_zero {q : ℝ} (hq : 0<q) :
    ContinuousAt (fun t : ℝ => t^(1/q)) 0 :=
  (continuous_id.rpow_const (fun _ => Or.inr (one_div_pos.mpr hq).le)).continuousAt

/-- Crossing the level τ of the metric distance to the Gaussian orbit, while
retaining precisely the initial relative lower bound on the Young moment. -/
theorem crossing_unit_input {n : ℕ} {s α τ : ℝ} (hs : 1<s) (hq : 1≤criticalExponent 1 s)
    [Fact (1≤ENNReal.ofReal (criticalExponent 1 s))] (hα : α<1) (hτ : 0<τ)
    (f : YoungUnitInput n (criticalExponent 1 s))
    (hNear : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s f.val)
    (hFar : τ ≤ Metric.infDist (f.toLp (zero_lt_one.trans_le hq))
      (unitGaussianSet n _ (zero_lt_one.trans_le hq))) :
    ∃ h : YoungUnitInput n (criticalExponent 1 s),
      ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s h.val ∧
      Metric.infDist (h.toLp (zero_lt_one.trans_le hq))
        (unitGaussianSet n _ (zero_lt_one.trans_le hq)) = τ := by
  let q := criticalExponent 1 s
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let S := unitGaussianSet n q hq0
  rcases hFar.eq_or_lt with he | hFar
  · exact ⟨f,hNear,he.symm⟩
  obtain ⟨u,hi,hn,hm,hfirst,hnear⟩ := diagonal_heat_path hs hα f.val f.meas f.mass hNear
  let U (t : ℝ) : YoungUnitInput n q :=
    ⟨densityRoot q (heatPath u t), densityRoot_aemeasurable (heatPath_integrable hi t).aemeasurable q,
     by rw [densityRoot_mass hq0 _ (heatPath_integrable hi t) (heatPath_nonneg hn t), heatPath_mass hi, hm]; simp⟩
  let z (t : ℝ) := (U t).toLp hq0
  let d (t : ℝ) := Metric.infDist (z t) S
  have h0 : z 0 = f.toLp hq0 := by
    apply Lp.ext
    have hd := densityRoot_first (q:=q) rfl hq0 hfirst
    filter_upwards [(U 0).toLp_coe hq0,f.toLp_coe hq0,hd] with x h₁ h₂ h₃
    rw [h₁,h₂]; exact_mod_cast (by simpa [U,heatPath] using h₃ : (U 0).val x=f.val x)
  have hinit : τ < d 0 := by simpa [d,h0,S] using hFar
  have hc : ContinuousOn z (Ici 0) := by
    intro t ht
    apply tendsto_iff_dist_tendsto_zero.2
    have hlim := (continuous_root_zero hq0).tendsto.comp (heatPath_L1_continuous hi hn ht)
    have he : Tendsto (fun t' => (∫ x, ‖heatPath u t' x-heatPath u t x‖)^(1/q)) (𝓝[Ici 0] t) (𝓝 0) := by
      simpa only [Function.comp_def, Real.zero_rpow (one_div_pos.mpr hq0).ne'] using hlim
    apply squeeze_zero (fun _ => dist_nonneg) _ he
    intro t'
    exact root_distance_bound hq _ _ (heatPath_integrable hi t') (heatPath_integrable hi t)
      (heatPath_nonneg hn t') (heatPath_nonneg hn t) (U t') (U t) rfl rfl
  have hK (t : ℝ) (ht : 0<t) : Integrable (heatGaussian (YoungHilbert n) t) := by
    apply Integrable.const_mul
    simpa using integrable_gaussian_shift (0:YoungHilbert n) (by positivity : 0 < (4*t)⁻¹)
  have hlarge : Tendsto (fun t : ℝ => (∫ x, ‖heatConvolution u t x - heatGaussian _ t x‖)^(1/q))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.zero_rpow (one_div_pos.mpr hq0).ne'] using
      (continuous_root_zero hq0).tendsto.comp (heatConvolution_large_time_L1 hi hn hm)
  obtain ⟨T,hT,hTsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and (hlarge.eventually_lt_const hτ)).exists
  have hend : d T ≤ τ := by
    have hdist := root_distance_bound hq (heatPath u T) (heatGaussian _ T) (heatPath_integrable hi T)
      (hK T hT) (heatPath_nonneg hn T) (fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (U T) (heatGaussianInput n hq0 hT) rfl rfl
    apply (Metric.infDist_le_dist_of_mem (heatGaussianInput_mem n q hq0 hT)).trans (hdist.trans ?_)
    simpa [heatPath,not_le.mpr hT] using hTsmall.le
  have hd : ContinuousOn d (Icc 0 T) :=
    ((Metric.continuous_infDist_pt S).comp_continuousOn hc).mono Icc_subset_Ici_self
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' hT.le hd (show τ ∈ Icc (d T) (d 0) from ⟨hend,hinit.le⟩)
  have ht' : 0<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  refine ⟨U t,?_,he⟩
  simpa [U,heatPath,not_le.mpr ht'] using hnear t ht'

end LpGowers
