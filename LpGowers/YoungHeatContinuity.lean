module

public import LpGowers.YoungHeatMoment
public import LpGowers.YoungHeatPath
import Mathlib.Tactic

/-! Continuity estimates for the critical roots of heat densities. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter GeometricBrascampLieb
open scoped ENNReal NNReal Topology
namespace LpGowers

theorem densityRoot_aemeasurable {n : ℕ} {u : YoungHilbert n → ℝ} (hu : AEMeasurable u volume) (q : ℝ) :
    AEMeasurable (densityRoot q u) (euclideanMeasure n) :=
  ((hu.comp_quasiMeasurePreserving (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving).real_toNNReal).pow_const _

theorem densityRoot_distance {n : ℕ} {q : ℝ} (hq : 1 ≤ q) {u v : YoungHilbert n → ℝ}
    (hu : Integrable u) (hv : Integrable v) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) :
    lpDist (euclideanMeasure n) q (densityRoot q u) (densityRoot q v) ≤
      (ENNReal.ofReal (∫ x, ‖u x - v x‖))^(1/q) := by
  let e := WithLp.toLp 2 (V:=Rn n)
  have hq0 := zero_lt_one.trans_le hq
  have hγ := one_div_pos.mpr hq0
  have h := lpDist_rpow_sublinear (euclideanMeasure n) (r:=1) zero_lt_one hγ
    ((div_le_one hq0).2 hq) (fun x => (u (e x)).toNNReal) (fun x => (v (e x)).toNNReal)
  have em : MeasurePreserving e (euclideanMeasure n) volume := PiLp.volume_preserving_toLp (Fin n)
  have hD : lpDist (euclideanMeasure n) 1 (fun x => (u (e x)).toNNReal) (fun x => (v (e x)).toNNReal) =
      ENNReal.ofReal (∫ x, ‖u x - v x‖) := by
    simp only [lpDist,lp,ENNReal.rpow_one,div_one]
    have hint : Integrable (fun x => ‖u x - v x‖) := (hu.sub hv).norm
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun _ => norm_nonneg _))]
    convert em.lintegral_comp' hint.aemeasurable.ennreal_ofReal using 1
    apply lintegral_congr
    intro x
    simp only [edist_dist, NNReal.dist_eq,Real.coe_toNNReal _ (hu0 _),Real.coe_toNNReal _ (hv0 _), Real.norm_eq_abs]
  rw [hD] at h
  change lpDist _ q (fun x => (u (WithLp.toLp 2 x)).toNNReal ^ (1/q)) (fun x => (v (WithLp.toLp 2 x)).toNNReal ^ (1/q)) ≤ _
  simpa only [one_div_one_div] using h

/-- Each point on the path represents the original critical density, or its heat flow. -/
theorem heatPath_integrable {n : ℕ} {u : YoungHilbert n → ℝ} (hi : Integrable u) (t : ℝ) :
    Integrable (heatPath u t) := by
  unfold heatPath
  split_ifs with h
  · exact hi
  · exact heatConvolution_integrable hi (lt_of_not_ge h)

theorem heatPath_nonneg {n : ℕ} {u : YoungHilbert n → ℝ} (hn : ∀ x, 0≤u x) (t : ℝ) (x) :
    0 ≤ heatPath u t x := by
  unfold heatPath
  split_ifs
  · exact hn x
  · exact mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg hn _ _)

theorem heatPath_mass {n : ℕ} {u : YoungHilbert n → ℝ} (hi : Integrable u) (t : ℝ) :
    (∫ x, heatPath u t x) = ∫ x,u x := by
  unfold heatPath
  split_ifs with h
  · rfl
  · exact integral_heatConvolution hi (lt_of_not_ge h)

theorem densityRoot_first {n : ℕ} {q s : ℝ} (hq : q = criticalExponent 1 s) (hq0 : 0 < q)
    {u : YoungHilbert n → ℝ} {F : Rn n → ℝ≥0} (h : u =ᵐ[volume] youngFirstDensity n s F) :
    densityRoot q u =ᵐ[euclideanMeasure n] F := by
  have he := (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [he] with x hx
  change u (WithLp.toLp 2 x) = ((F x : ℝ)^criticalExponent 1 s) at hx
  simp only [densityRoot,hx, ← hq, ← NNReal.coe_rpow, Real.toNNReal_coe,
    ← NNReal.rpow_mul, mul_one_div_cancel hq0.ne', NNReal.rpow_one]

end LpGowers
