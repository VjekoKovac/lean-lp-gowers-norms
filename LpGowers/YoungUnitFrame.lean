module

public import LpGowers.YoungExtremalLift
public import LpGowers.YoungHeatDeficit
import Mathlib.Tactic

/-! # Unit-mass geometric and heat deficits for diagonal Young near-extremizers

The nonlinear dual row may be multiplied by a positive constant without
changing its Brascamp–Lieb ratio. Normalizing that row gives a uniform
absolute heat error for the inputs in the completed Lebesgue measure.
-/

@[expose] public section
noncomputable section
open MeasureTheory GeometricBrascampLieb
open scoped ENNReal NNReal BigOperators
namespace LpGowers

/-- A normalized near-extremizer lifts to three unit-mass densities. The first
two agree, and the lower bound for the geometric integral is dimension-free. -/
theorem unit_frame_of_diagonal {n : ℕ} {s α : ℝ} (hs : 1<s) (hα : α<1)
    (F : Rn n → ℝ≥0) (hf : AEMeasurable F (euclideanMeasure n))
    (hm : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hNear : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s F) :
    ∃ u v : YoungHilbert n → ℝ, u =ᵐ[volume] youngFirstDensity n s F ∧
      Integrable u ∧ Integrable v ∧ (∀ y, 0≤u y) ∧ (∀ y, 0≤v y) ∧
      (∫ y, u y)=1 ∧ (∫ y, v y)=1 ∧
      (1-α)^(1/s) ≤ ∫ z : YoungPair n, ∏ i,
        ((![u,u,v] i) (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i := by
  let μ := euclideanMeasure n
  let G := hf.mk F
  have hG : F =ᵐ[μ] G := hf.ae_eq_mk
  have hGm : (∫⁻ x, (G x : ℝ≥0∞)^criticalExponent 1 s ∂μ) = 1 := by
    apply Eq.trans _ hm
    exact lintegral_congr_ae (hG.mono fun _ h => by simp [h])
  have hn : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s G := by
    apply hNear.trans_eq
    unfold cubeMoment
    have : μ.IsAddLeftInvariant := by dsimp [μ,euclideanMeasure]; infer_instance
    rw [autocorrelation_congr_ae μ hG]
  obtain ⟨v,hu,hv,hu0,hv0,hum,hvm,hGeo⟩ := frame_near_of_diagonal hs hα G hf.measurable_mk hGm hn
  let u := youngFirstDensity n s G
  let m := ∫ y, v y
  let w := youngFrameWeight s (2 : Fin 3)
  let v' := fun y => m⁻¹*v y
  have hm0 : 0 < m := hvm
  have he : MeasurePreserving (WithLp.ofLp : YoungHilbert n → Rn n) volume μ :=
    PiLp.volume_preserving_ofLp (Fin n)
  refine ⟨u,v',?_,hu,hv.const_mul _,hu0,(fun y => mul_nonneg (inv_nonneg.mpr hm0.le) (hv0 y)),hum,?_,?_⟩
  · have h := he.quasiMeasurePreserving.ae_eq_comp hG
    filter_upwards [h] with y hy
    simp only [Function.comp_apply] at hy
    simp only [u,youngFirstDensity,hy]
  · change (∫ y, m⁻¹*v y) = 1
    rw [integral_const_mul,show (∫ y,v y) = m from rfl,inv_mul_cancel₀ hm0.ne']
  · let P := fun z : YoungPair n => ∏ i, ((![u,u,v] i)
        (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i
    have hp (z : YoungPair n) : (∏ i, ((![u,u,v'] i)
        (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i) = (m⁻¹)^w*P z := by
      dsimp only [P]
      rw [Fin.prod_univ_three,Fin.prod_univ_three]
      let A := u (youngFrameMap (YoungHilbert n) s 0 z)^youngFrameWeight s 0
      let B := u (youngFrameMap (YoungHilbert n) s 1 z)^youngFrameWeight s 1
      let C := v (youngFrameMap (YoungHilbert n) s 2 z)
      change A*B*(m⁻¹*C)^w = (m⁻¹)^w*(A*B*C^w)
      rw [Real.mul_rpow (inv_nonneg.mpr hm0.le) (hv0 _)]
      ring
    have hM : (∏ i, (∫ y, (![u,u,v] i) y)^youngFrameWeight s i) = m^w := by
      rw [Fin.prod_univ_three]
      change (∫ y,u y)^_*(∫ y,u y)^_*m^w = m^w
      rw [hum,Real.one_rpow,Real.one_rpow,one_mul,one_mul]
    change (1-α)^(1/s)* (∏ i, (∫ y, (![u,u,v] i) y)^youngFrameWeight s i) ≤ ∫ z, P z at hGeo
    rw [hM] at hGeo
    simp_rw [hp]
    rw [integral_const_mul,Real.inv_rpow hm0.le,← div_eq_inv_mul]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hm0 w)).2 hGeo

/-- The difference between smoothing the product and multiplying the smoothed
rows has small L¹ norm uniformly over all positive times. -/
theorem heat_error_of_near_diagonal {n : ℕ} {s α : ℝ} (hs : 1<s) (hα : α<1)
    (F : Rn n → ℝ≥0) (hf : AEMeasurable F (euclideanMeasure n))
    (hm : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hNear : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s F) :
    ∃ u v : YoungHilbert n → ℝ, u =ᵐ[volume] youngFirstDensity n s F ∧
      Integrable u ∧ Integrable v ∧ (∀ y, 0≤u y) ∧ (∀ y, 0≤v y) ∧
      (∫ y, u y)=1 ∧ (∫ y, v y)=1 ∧ ∀ t : ℝ, 0<t →
      let B := youngFrameMap (YoungHilbert n) s
      let g := fun z : YoungPair n => ∏ i, ((![u,u,v] i) (B i z))^youngFrameWeight s i
      let h := fun z : YoungPair n => ∏ i, (heatConvolution (![u,u,v] i) t (B i z))^youngFrameWeight s i
      (∫ z : YoungPair n, |h z-heatConvolution g t z|) ≤ 1-(1-α)^(1/s) := by
  obtain ⟨u,v,huF,hu,hv,hu0,hv0,hum,hvm,hG⟩ := unit_frame_of_diagonal hs hα F hf hm hNear
  refine ⟨u,v,huF,hu,hv,hu0,hv0,hum,hvm,?_⟩
  intro t ht
  let V := YoungHilbert n
  let D : Datum (Fin 3) (YoungPair n) (fun _ => V) :=
    .ofNormSq (youngFrameMap V s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry V (zero_lt_one.trans hs)) (youngFrameMap_resolution V (zero_lt_one.trans hs))
  let f : Fin 3 → V → ℝ := ![u,u,v]
  have hi i : Integrable (f i) := by fin_cases i <;> first | exact hu | exact hv
  have hn i : ∀ y, 0≤ f i y := by fin_cases i <;> first | exact hu0 | exact hv0
  have hMass i : (∫ y, f i y) = 1 := by fin_cases i <;> first | exact hum | exact hvm
  apply (heat_error_le_initial_deficit D hi hn ht).trans
  apply sub_le_sub
  · simp [hMass]
  · exact hG

end LpGowers
