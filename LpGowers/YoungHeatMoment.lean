module

public import LpGowers.YoungUnitFrame
import LpGowers.Interpolation
import Mathlib.Tactic

/-! A lower bound for the geometric Young integral gives a lower bound
for the first row's autocorrelation norm, by ordinary Hölder duality.
Consequently taking the heat flow of the critical density preserves every
relative lower bound on the diagonal objective. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter GeometricBrascampLieb
open scoped ENNReal NNReal BigOperators
namespace LpGowers

/-- The diagonal objective controls the geometric pairing against any unit density. -/
theorem geometric_pairing_le_diagonal {n : ℕ} {s : ℝ} (hs : 1 < s)
    (F : Rn n → ℝ≥0) (hF : Measurable F) (V : YoungHilbert n → ℝ≥0∞)
    (hV : Measurable V) (hVm : (∫⁻ y, V y) = 1) :
    let q := criticalExponent 1 s
    let U₀ := fun y : YoungHilbert n => (F (WithLp.ofLp y) : ℝ≥0∞)^q
    let U : Fin 3 → YoungHilbert n → ℝ≥0∞ := ![U₀,U₀,V]
    (∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i) *
      (youngMomentConstant 1 n s)^(1/s) ≤ (cubeMoment 1 n s F)^(1/s) := by
  intro q U₀ U
  let μ := euclideanMeasure n
  let R := pairCorrelation μ (liftNN F) (liftNN F)
  let a := youngFrameA s
  let b := youngFrameB s
  let v := (s-1)/s
  let w := (s+1)/(2*s)
  let D := youngDilation n (2*a)
  let k := youngDilation n b * D
  let H₀ := fun t : Rn n => V (WithLp.toLp 2 ((2*a)⁻¹ • t))
  let H := fun t => H₀ t ^ v
  let J := ∫⁻ t, R t ^ s ∂μ
  have hs0 := zero_lt_one.trans hs
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have ha' : 0<2*a := by positivity
  have hv : 0<v := div_pos (sub_pos.mpr hs) hs0
  have hr : 0 < 1/s := one_div_pos.mpr hs0
  have hvsum : 1/s+v=1 := by dsimp [v]; field_simp; ring
  have hqw : q*w=1 := by dsimp [q,w,criticalExponent]; norm_num; field_simp; ring
  have hf' : Measurable (liftNN F) := hF.coe_nnreal_ennreal
  have : SigmaFinite μ := by dsimp [μ,euclideanMeasure]; infer_instance
  have hR : Measurable R := Measurable.lintegral_prod_right
    ((hf'.comp measurable_snd).mul (hf'.comp (measurable_snd.add measurable_fst)))
  have mapY : MeasurePreserving (WithLp.toLp 2 : Rn n → YoungHilbert n) μ volume :=
    PiLp.volume_preserving_toLp (Fin n)
  have he : MeasurePreserving (WithLp.ofLp : YoungHilbert n → Rn n) volume μ :=
    PiLp.volume_preserving_ofLp (Fin n)
  have hpair : MeasurePreserving (fun z : YoungPair n => (WithLp.ofLp z.fst,WithLp.ofLp z.snd)) volume (μ.prod μ) := (he.prod he).comp (WithLp.volume_preserving_ofLp (YoungHilbert n) (YoungHilbert n))
  have hH₀ : Measurable H₀ := (hV.comp mapY.measurable).comp (measurable_const_smul _)
  have hH : Measurable H := hH₀.pow_const _
  have hDm : ∫⁻ t, H₀ t ∂μ = D⁻¹ := by
    rw [show (∫⁻ t, H₀ t ∂μ) = youngDilation n (2*a)⁻¹ * (∫⁻ t : Rn n,V (WithLp.toLp 2 t) ∂μ)
      from young_lintegral_smul n (inv_pos.mpr ha') _ (hV.comp mapY.measurable),
      mapY.lintegral_comp hV,hVm,mul_one]
    simp only [D,youngDilation,inv_pow,inv_inv]
    rw [ENNReal.ofReal_inv_of_pos (pow_pos ha' _),inv_inv]
  let P := fun z : Rn n × Rn n =>
    liftNN F ((-a)•z.1+b•z.2)*liftNN F (a•z.1+b•z.2)* H ((2*a)•z.1)
  have hP : Measurable P := by dsimp only [P]; fun_prop
  have hpoint (z : YoungPair n) : (∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i) =
      P (WithLp.ofLp z.fst,WithLp.ofLp z.snd) := by
    rw [Fin.prod_univ_three]
    change (_^q)^w * (_^q)^w * (V ((1:ℝ)• z.fst+(0:ℝ)•z.snd))^v = _
    simp only [P,H,H₀,← ENNReal.rpow_mul,hqw,ENNReal.rpow_one,one_smul,zero_smul,add_zero,
      inv_smul_smul₀ ha'.ne', WithLp.toLp_ofLp]
    rfl
  have hpairing : (∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i) =
      k * ∫⁻ t, R t * H t ∂μ := by
    simp_rw [hpoint]; rw [hpair.lintegral_comp hP]
    exact young_frame_change_variables n ha hb _ _ _ hf' hf' hH
  have hholder : (∫⁻ t, R t * H t ∂μ) ≤ J^(1/s) * (D⁻¹)^v := by
    have h := ENNReal.lintegral_mul_norm_pow_le (μ:=μ) (hR.pow_const s).aemeasurable hH₀.aemeasurable hr.le hv.le hvsum
    simpa only [← ENNReal.rpow_mul,mul_one_div_cancel hs0.ne',ENNReal.rpow_one,hDm] using h
  have hk : k≠0 := by dsimp [k,D,youngDilation]; positivity
  have hkt : k≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hD : D≠0 := by dsimp [D,youngDilation]; positivity
  have hDt : D≠⊤ := ENNReal.ofReal_ne_top
  rw [hpairing,cubeMoment_one n s F hF.aemeasurable,youngMomentConstant_one,
    ← young_dilation_constant n s hs]
  change (k * _) * (k⁻¹ * D^v) ≤ J^(1/s)
  calc
    _ ≤ (k*(J^(1/s)*(D⁻¹)^v))*(k⁻¹*D^v) := by gcongr
    _ = (k*k⁻¹)*((D^v)⁻¹*D^v)*J^(1/s) := by rw [ENNReal.inv_rpow]; ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hk hkt, ENNReal.inv_mul_cancel
                           ((ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hD) hv.le).ne')
                           (ENNReal.rpow_ne_top_of_nonneg hv.le hDt),one_mul,one_mul]

/-- Recover the Young input from its critical density in orthonormal coordinates. -/
def densityRoot {n : ℕ} (q : ℝ) (u : YoungHilbert n → ℝ) (x : Rn n) : ℝ≥0 :=
  (u (WithLp.toLp 2 x)).toNNReal ^ (1/q)

theorem densityRoot_measurable {n : ℕ} {u : YoungHilbert n → ℝ} (hu : Measurable u) (q : ℝ) :
    Measurable (densityRoot q u) :=
  ((hu.comp (PiLp.volume_preserving_toLp (Fin n)).measurable).real_toNNReal).pow_const _

theorem densityRoot_mass {n : ℕ} {q : ℝ} (hq : 0 < q) (u : YoungHilbert n → ℝ)
    (hu : Integrable u) (h₀ : ∀ x, 0 ≤ u x) :
    ∫⁻ x, (densityRoot q u x : ℝ≥0∞)^q ∂euclideanMeasure n = ENNReal.ofReal (∫ x, u x) := by
  have hp (x : Rn n) : (densityRoot q u x : ℝ≥0∞)^q = ENNReal.ofReal (u (WithLp.toLp 2 x)) := by
    simp only [densityRoot, ENNReal.coe_rpow_of_nonneg _ (one_div_pos.mpr hq).le,
      ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one, ENNReal.ofReal]
  simp_rw [hp]
  rw [ofReal_integral_eq_lintegral_ofReal hu (Eventually.of_forall h₀)]
  exact (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp' hu.aemeasurable.ennreal_ofReal

private theorem frame_lower_to_moment {n : ℕ} {s α : ℝ} (hs : 1<s) (hα : α<1)
    (u v : YoungHilbert n → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hUi : Integrable u) (hVi : Integrable v) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hVm : (∫ x,v x) = 1)
    (hG : (1-α)^(1/s) ≤ ∫ z : YoungPair n, ∏ i, ((![u,u,v] i)
        (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i) :
    ENNReal.ofReal (1-α) * youngMomentConstant 1 n s ≤
      cubeMoment 1 n s (densityRoot (criticalExponent 1 s) u) := by
  let q := criticalExponent 1 s
  let D : Datum (Fin 3) (YoungPair n) (fun _ => YoungHilbert n) :=
    .ofNormSq (youngFrameMap _ s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry _ (zero_lt_one.trans hs)) (youngFrameMap_resolution _ (zero_lt_one.trans hs))
  let f : Fin 3 → YoungHilbert n → ℝ := ![u,u,v]
  let B := fun z : YoungPair n => ∏ i, (f i (D.map i z))^D.weight i
  have hFi i : Integrable (f i) := by fin_cases i <;> first | exact hUi | exact hVi
  have hF0 i : ∀ y, 0≤ f i y := by fin_cases i <;> first | exact hu0 | exact hv0
  have hBi : Integrable B := D.integrable_prod_of_integrable hFi hF0
  have hB0 z : 0≤B z := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hF0 i _) _
  let V := fun x => ENNReal.ofReal (v x)
  have hV1 : ∫⁻ x, V x = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hVi (Eventually.of_forall hv0),hVm,ENNReal.ofReal_one]
  let F := densityRoot q u
  let U₀ := fun y : YoungHilbert n => (F (WithLp.ofLp y) : ℝ≥0∞)^q
  let U : Fin 3 → YoungHilbert n → ℝ≥0∞ := ![U₀,U₀,V]
  have hq : 0<q := by have := zero_lt_one.trans hs; dsimp [q,criticalExponent]; positivity
  have hU i y : U i y = ENNReal.ofReal (f i y) := by
    have hh : U₀ y = ENNReal.ofReal (u y) := by
      simp only [U₀,F,densityRoot, WithLp.toLp_ofLp, ENNReal.coe_rpow_of_nonneg _ (one_div_pos.mpr hq).le,
        ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one, ENNReal.ofReal]
    fin_cases i <;> first | exact hh | rfl
  have hB z : ENNReal.ofReal (B z) =
      ∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hF0 i _) _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [hU, ← ENNReal.ofReal_rpow_of_nonneg (hF0 i _) (D.weight_nonneg i)]
    rfl
  have hLow := ENNReal.ofReal_le_ofReal hG
  change ENNReal.ofReal ((1-α)^(1/s)) ≤ ENNReal.ofReal (∫ z, B z) at hLow
  rw [ofReal_integral_eq_lintegral_ofReal hBi (Eventually.of_forall hB0)] at hLow
  simp_rw [hB] at hLow
  have hr := one_div_pos.mpr (zero_lt_one.trans hs)
  apply (ENNReal.rpow_le_rpow_iff hr).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hα.le) hr.le]
  exact (mul_le_mul_left hLow _).trans
    (geometric_pairing_le_diagonal hs F (densityRoot_measurable hu q) V hv.ennreal_ofReal hV1)

/-- Heat flow of the first density preserves the original relative diagonal Young bound. -/
theorem diagonal_heat_path {n : ℕ} {s α : ℝ} (hs : 1 < s) (hα : α < 1)
    (F : Rn n → ℝ≥0) (hf : AEMeasurable F (euclideanMeasure n))
    (hm : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hNear : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s F) :
    ∃ u : YoungHilbert n → ℝ, Integrable u ∧ (∀ x, 0 ≤ u x) ∧ (∫ x, u x) = 1 ∧
      u =ᵐ[volume] youngFirstDensity n s F ∧
      ∀ t : ℝ, 0<t → ENNReal.ofReal (1-α) * youngMomentConstant 1 n s ≤
        cubeMoment 1 n s (densityRoot (criticalExponent 1 s) (heatConvolution u t)) := by
  obtain ⟨u,v,he,hu,hv,hu₀,hv₀,hum,hvm,hG⟩ := unit_frame_of_diagonal hs hα F hf hm hNear
  refine ⟨u, hu, hu₀, hum, he, ?_⟩
  intro t ht
  let f : Fin 3 → YoungHilbert n → ℝ := ![u,u,v]
  let D : Datum (Fin 3) (YoungPair n) (fun _ => YoungHilbert n) :=
    .ofNormSq (youngFrameMap _ s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry _ (zero_lt_one.trans hs)) (youngFrameMap_resolution _ (zero_lt_one.trans hs))
  have hFi i : Integrable (f i) := by fin_cases i <;> first | exact hu | exact hv
  have hF0 i : ∀ y, 0≤ f i y := by fin_cases i <;> first | exact hu₀ | exact hv₀
  have hnn {g : YoungHilbert n → ℝ} (hg : ∀ x, 0 ≤ g x) : ∀ x, 0 ≤ heatConvolution g t x :=
    fun _ => mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg hg _ _)
  apply frame_lower_to_moment hs hα _ (heatConvolution v t) (heatConvolution_continuous hu ht).measurable
    (heatConvolution_continuous hv ht).measurable (heatConvolution_integrable hu ht)
    (heatConvolution_integrable hv ht) (hnn hu₀) (hnn hv₀) ((integral_heatConvolution hv ht).trans hvm)
  let B := fun z : YoungPair n => ∏ i, (f i (D.map i z))^D.weight i
  let W := fun i => heatConvolution (f i) t
  have bi : Integrable B := D.integrable_prod_of_integrable hFi hF0
  have hsmooth := integral_mono (heatConvolution_integrable bi ht)
     (D.integrable_prod_of_integrable (fun i => heatConvolution_integrable (hFi i) ht) (fun i => hnn (hF0 i)))
     (heatConvolution_prod_le D hFi hF0 ht)
  rw [integral_heatConvolution bi ht] at hsmooth
  have hw (i : Fin 3) : W i = (![heatConvolution u t,heatConvolution u t,heatConvolution v t] i) := by
    fin_cases i <;> rfl
  change _ ≤ ∫ z, ∏ i, (W i (D.map i z))^D.weight i at hsmooth
  simp_rw [hw] at hsmooth
  exact hG.trans hsmooth

end LpGowers
