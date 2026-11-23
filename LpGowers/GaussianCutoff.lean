module

public import LpGowers.EuclideanAffine
public import LpGowers.MonotoneApproximation
import LpGowers.Nonvanishing
import LpGowers.Scaling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Compactly supported one-dimensional test functions for the lower bound
in Theorem 1.5(b). Continuous cutoffs increase to the Gaussian, and an
affine change of variables puts each test in the open unit interval. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

private theorem scalar_gaussian_ratio (d : ℕ) {p : ℝ} (hp : 0<p) :
    let q := criticalExponent d p
    let N := lp volume q (liftNN (scalarGaussian 1))
    0<N ∧ N<⊤ ∧ gowers volume d p (scalarGaussian 1) =
      ENNReal.ofReal (sharpEuclideanConstant d 1 p) * N := by
  let q := criticalExponent d p
  have hq : 0<q := by dsimp [q,criticalExponent]; positivity
  let T : Rn 1 →+ ℝ := ⟨⟨fun x => x default, rfl⟩, fun _ _ => rfl⟩
  let μ := euclideanMeasure 1
  have hm : μ.map T = volume := (measurePreserving_piUnique (fun _ : Fin 1 => (volume : Measure ℝ))).map_eq
  have : SigmaFinite (μ.map T) := hm ▸ inferInstance
  have hT : Measurable T := measurable_pi_apply _
  have hF : Measurable (scalarGaussian 1) := by unfold scalarGaussian; fun_prop
  have hg : (fun x => scalarGaussian 1 (T x)) = tensorGaussian 1 1 := by
    funext x
    simp [tensorGaussian,T]
  have hU := gowers_comp_addHom μ T hT d p _ hF
  rw [hg,hm] at hU
  have hN : lp μ q (liftNN (tensorGaussian 1 1)) = lp volume q (liftNN (scalarGaussian 1)) := by
    rw [← hg]
    unfold lp liftNN
    congr 1
    have m : Measurable (fun x => ((scalarGaussian 1 x : ℝ≥0∞))^q) := by fun_prop
    exact (lintegral_map m hT).symm.trans (by rw [hm])
  have h := gaussian_test_equality_scaled d 1 1 p (by norm_num) hp
  change gowers μ d p (tensorGaussian 1 1) = _ * lp μ q _ at h
  rw [hN,hU] at h
  have hval := lp_tensorGaussian 1 1 q (by norm_num) hq
  change lp μ q (liftNN (tensorGaussian 1 1)) = _ at hval
  dsimp only
  change 0 < lp volume q _ ∧ lp volume q _ < ⊤ ∧ _ = _ * lp volume q _
  rw [← hN, hval, pow_one]
  refine ⟨?_,?_,?_⟩
  · exact ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (by positivity))) (by positivity)
  · exact (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top).lt_top
  · simpa only [← hN,hval,pow_one] using h

private def cutGaussian (n : ℕ) (x : ℝ) : ℝ≥0 :=
  scalarGaussian 1 x * min 1 (((n:ℝ)-|x|).toNNReal)

private theorem continuous_cutGaussian (n : ℕ) : Continuous (cutGaussian n) := by
  unfold cutGaussian scalarGaussian
  fun_prop

private theorem cutGaussian_le (n : ℕ) (x : ℝ) : cutGaussian n x ≤ scalarGaussian 1 x :=
  (mul_le_mul_right (min_le_left _ _) _).trans_eq (mul_one _)

private theorem affine_ratio {d : ℕ} {p s : ℝ} (hp : 0<p) (hs : 0<s)
    (v : ℝ → ℝ≥0) (hv : Measurable v) {r : ℝ}
    (hr : ENNReal.ofReal r * lp volume (criticalExponent d p) (liftNN v) < gowers volume d p v) :
    let f := fun x => v (s*(x-1/2))
    ENNReal.ofReal r * lp volume (criticalExponent d p) (liftNN f) < gowers volume d p f := by
  let q := criticalExponent d p
  have hq : 0<q := by dsimp [q,criticalExponent]; positivity
  let T := AddMonoidHom.mulLeft s
  let c := s⁻¹.toNNReal
  have hc : 0<c := Real.toNNReal_pos.mpr (inv_pos.mpr hs)
  have hT : Measurable T := measurable_const.mul measurable_id
  have hmap : (volume : Measure ℝ).map T = c • volume := by
    change Measure.map (fun x : ℝ => s*x) volume = c • volume
    rw [Real.map_volume_mul_left hs.ne',abs_of_pos (inv_pos.mpr hs)]
    rfl
  have : SigmaFinite ((volume : Measure ℝ).map T) := hmap ▸ inferInstance
  let F := v ∘ T
  have hu : gowers volume d p F = (c:ℝ≥0∞)^(1/q) * gowers volume d p v := by
    rw [show gowers volume d p F = gowers (volume.map T) d p v from gowers_comp_addHom volume T hT d p v hv,
      hmap,gowers_smul_measure _ c d v hp]
    congr 2
    dsimp [q,criticalExponent]
    field_simp
  have hlp := lp_comp_smulMeasure volume T hT c hmap v hv q hq
  have hd := ENNReal.mul_lt_mul_right
    (ENNReal.rpow_pos_of_nonneg (ENNReal.coe_pos.mpr hc) (one_div_nonneg.mpr hq.le)).ne'
    (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hq.le) ENNReal.coe_ne_top) hr
  change ENNReal.ofReal r * lp volume q (liftNN (fun x => F (x + -(1/2)))) <
    gowers volume d p (fun x => F (x + -(1/2)))
  rw [lp_translate, gowers_translate,hlp,hu,mul_left_comm]
  exact hd

/-- Every constant strictly below the exact Gaussian ratio is exceeded by
a continuous nonnegative test supported in the unit interval and bounded
pointwise by one. -/
theorem exists_unit_interval_gaussian_test (d : ℕ) {p r : ℝ} (hp : 0<p)
    (hr : 0<r) (hrC : r < sharpEuclideanConstant d 1 p) :
    ∃ f : ℝ → ℝ≥0, Continuous f ∧ Function.support f ⊆ Set.Ioo 0 1 ∧
      (∀ x, f x ≤ 1) ∧ 0 < lp volume (criticalExponent d p) (liftNN f) ∧
      lp volume (criticalExponent d p) (liftNN f) < ⊤ ∧ gowers volume d p f < ⊤ ∧
      ENNReal.ofReal r * lp volume (criticalExponent d p) (liftNN f) < gowers volume d p f := by
  let G := scalarGaussian 1
  let q := criticalExponent d p
  have hq : 0<q := by dsimp [q,criticalExponent]; positivity
  obtain ⟨hN,hNt,he⟩ := scalar_gaussian_ratio d hp
  have ho : Monotone cutGaussian := by
    intro i j hij x
    apply mul_le_mul_right (min_le_min_left _ ?_) _
    exact Real.toNNReal_le_toNNReal (sub_le_sub_right (Nat.cast_le.mpr hij) _)
  have hsup (x : ℝ) : (G x : ℝ≥0∞) = ⨆ n, (cutGaussian n x : ℝ≥0∞) := by
    obtain ⟨n,hn⟩ := exists_nat_ge (|x|+1)
    have hnn : (1:ℝ≥0) ≤ ((n:ℝ)-|x|).toNNReal := by
      rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal (by linarith)
    refine le_antisymm (le_iSup_of_le n ?_) (iSup_le fun n => ENNReal.coe_le_coe.mpr (cutGaussian_le n x))
    simp [cutGaussian,G,min_eq_left hnn]
  have hG := gowers_monotone_convergence volume G cutGaussian ho
    (fun n => (continuous_cutGaussian n).measurable.aemeasurable) hsup d hp
  have hlt : ENNReal.ofReal r * lp volume q (liftNN G) < ⨆ n, gowers volume d p (cutGaussian n) := by
    rw [← hG,he]
    exact ENNReal.mul_lt_mul_left hN.ne' hNt.ne ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrC)).mpr hrC)
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp hlt
  have hnorm : lp volume q (liftNN (cutGaussian n)) ≤ lp volume q (liftNN G) := by
    unfold lp
    gcongr with x
    exact ENNReal.coe_le_coe.mpr (cutGaussian_le n x)
  let s : ℝ := 2*((n:ℝ)+1)
  have hs : 0<s := by dsimp [s]; positivity
  let f := fun x => cutGaussian n (s*(x-1/2))
  have hf : Continuous f := (continuous_cutGaussian n).comp (by fun_prop)
  have hc := affine_ratio hp hs _ (continuous_cutGaussian n).measurable ((mul_le_mul_right hnorm _).trans_lt hn)
  have hfge : 0 < gowers volume d p f := zero_le.trans_lt hc
  have hup (x) : f x ≤ G (s*(x-1/2)) := cutGaussian_le _ _
  let T := AddMonoidHom.mulLeft s
  let b := s⁻¹.toNNReal
  have hT : Measurable T := measurable_const.mul measurable_id
  have hmap : (volume : Measure ℝ).map T = b • volume := by
    change Measure.map (fun x : ℝ => s*x) volume = b • volume
    rw [Real.map_volume_mul_left hs.ne',abs_of_pos (inv_pos.mpr hs)]
    rfl
  have : SigmaFinite ((volume : Measure ℝ).map T) := hmap ▸ inferInstance
  have hgm : Measurable G := by unfold G scalarGaussian; fun_prop
  have hb : gowers volume d p f < ⊤ := by
    apply (gowers_mono volume hup d hp).trans_lt
    change gowers volume d p (fun x => (G ∘ T) (x + -(1/2))) < ⊤
    rw [gowers_translate, show gowers volume d p (G ∘ T) = gowers (volume.map T) d p G from
      gowers_comp_addHom volume T hT d p G hgm,hmap,gowers_smul_measure _ b d G hp,he]
    apply ENNReal.mul_lt_top
    · exact (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top).lt_top
    · exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNt.ne).lt_top
  have hnormtop : lp volume q (liftNN f) < ⊤ := by
    by_contra! hh
    have ht := top_le_iff.mp hh
    change ENNReal.ofReal r * lp volume q (liftNN f) < gowers volume d p f at hc
    rw [ht,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hr).ne'] at hc
    exact not_lt_of_ge le_top hc
  have hnormpos : 0 < lp volume q (liftNN f) := by
    refine pos_iff_ne_zero.mpr fun hz => ?_
    have hfm : AEMeasurable (liftNN f) volume := by unfold liftNN; fun_prop
    have hzero := (lp_eq_zero_iff volume hfm hq).mp hz
    have hh : f =ᵐ[volume] 0 := by
      filter_upwards [hzero] with x hx
      exact ENNReal.coe_eq_zero.mp hx
    exact hfge.ne' ((gowers_eq_zero_iff volume d hp hf.measurable.aemeasurable).mpr hh)
  refine ⟨f,hf,?_,?_,hnormpos,hnormtop,hb,hc⟩
  · intro x hx
    have hh : |s*(x-1/2)| < n := by
      by_contra! h
      have hz : (n:ℝ) - |s*(x-1/2)| ≤ 0 := sub_nonpos.mpr h
      exact hx (by simp only [f,cutGaussian,Real.toNNReal_of_nonpos hz, min_eq_right (by norm_num : (0:ℝ≥0)≤1), mul_zero])
    obtain ⟨hl,hu⟩ := abs_lt.mp hh
    have he : s/2 = (n:ℝ)+1 := by dsimp [s]; ring
    constructor
    · by_contra! h
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos hs.le h,hl,he]
    · by_contra! h
      nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr h),hu,he]
  · intro x
    apply (cutGaussian_le _ _).trans
    unfold scalarGaussian
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (s*(x-1/2))]))

end LpGowers
