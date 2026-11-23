module

public import LpGowers.YoungFrame
public import LpGowers.YoungTrilinearDefs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic

/-! # The Jacobian and the sharp Young constant

Splitting the geometric frame integral into two Euclidean variables gives
one translation and the two dilations by `b` and `2a`. Their Jacobians
and the dual test-function exponent give Beckner's factor.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

def youngDilation (n : ℕ) (c : ℝ) : ℝ≥0∞ := ENNReal.ofReal (c^n)⁻¹

theorem young_lintegral_smul (n : ℕ) {c : ℝ} (hc : 0<c) (F : Rn n → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F (c • x) ∂euclideanMeasure n) = youngDilation n c * ∫⁻ x, F x ∂euclideanMeasure n := by
  let μ := euclideanMeasure n
  let : μ.IsAddHaarMeasure := by dsimp [μ,euclideanMeasure]; infer_instance
  have hf : Module.finrank ℝ (Rn n) = n := by simp [Rn]
  rw [← lintegral_map hF (measurable_const_smul c),Measure.map_addHaar_smul μ hc.ne',
    lintegral_smul_measure,hf,abs_of_pos (inv_pos.mpr (pow_pos hc n))]
  rfl

theorem young_frame_change_variables (n : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (F G H : Rn n → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) :
    let μ := euclideanMeasure n
    (∫⁻ z : Rn n × Rn n, F ((-a) • z.1+b • z.2) * G (a • z.1+b • z.2) * H ((2*a) • z.1)
      ∂μ.prod μ) = (youngDilation n b * youngDilation n (2*a)) *
        ∫⁻ t, (∫⁻ x, F x*G (x+t) ∂μ) * H t ∂μ := by
  intro μ
  let : SigmaFinite μ := by dsimp [μ,euclideanMeasure]; infer_instance
  let : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  let C := fun t => ∫⁻ x, F x*G (x+t) ∂μ
  have hC : Measurable C := Measurable.lintegral_prod_right
    ((hF.comp measurable_snd).mul (hG.comp (measurable_snd.add measurable_fst)))
  let P := fun z : Rn n × Rn n => F ((-a) • z.1+b • z.2) * G (a • z.1+b • z.2) * H ((2*a) • z.1)
  have hP : Measurable P := by dsimp [P]; fun_prop
  rw [lintegral_prod P hP.aemeasurable]
  have inner (w : Rn n) : (∫⁻ z, P (w,z) ∂μ) = youngDilation n b * (C ((2*a) • w)*H ((2*a) • w)) := by
    let t := (2*a) • w
    let T := fun x => F x*G (x+t)*H t
    have hT : Measurable T := (hF.mul (hG.comp (measurable_id.add_const t))).mul_const _
    have point (z : Rn n) : P (w,z) = T ((b • z)+(-a) • w) := by
      dsimp only [P,T,t]
      rw [add_comm (b • z) ((-a) • w)]
      have hx : (-a) • w + b • z + (2*a) • w = a • w + b • z := by module
      rw [hx]
    simp_rw [point]
    have scale := young_lintegral_smul n hb (fun y => T (y+(-a) • w))
      (hT.comp (measurable_id.add_const _))
    change (∫⁻ z, (fun y => T (y+(-a) • w)) (b • z) ∂μ) = _
    rw [scale,lintegral_add_right_eq_self]
    change youngDilation n b * (∫⁻ x, F x*G (x+t)*H t ∂μ) = _
    rw [lintegral_mul_const (μ := μ) (f := fun x => F x*G (x+t)) (H t) (hF.mul (hG.comp (measurable_id.add_const _)))]
  simp_rw [inner]
  rw [lintegral_const_mul' (μ := μ) (youngDilation n b) (fun w => C ((2*a) • w)*H ((2*a) • w)) ENNReal.ofReal_ne_top]
  rw [show (∫⁻ w, C ((2*a) • w)*H ((2*a) • w) ∂μ) =
    youngDilation n (2*a) * ∫⁻ t, C t*H t ∂μ from
    young_lintegral_smul n (by positivity) (fun t => C t*H t) (hC.mul hH),mul_assoc]

theorem young_dilation_constant (n : ℕ) (s : ℝ) (hs : 1<s) :
    let a := youngFrameA s
    let b := youngFrameB s
    (youngDilation n b * youngDilation n (2*a))⁻¹ * (youngDilation n (2*a))^((s-1)/s) =
      (ENNReal.ofReal (diagonalYoungFactor s)^n)^(1/s) := by
  intro a b
  have hs0 := zero_lt_one.trans hs
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have h2a : 0<2*a := by positivity
  have hfac : 0 < diagonalYoungFactor s := by dsimp [diagonalYoungFactor]; positivity
  have hdil (c : ℝ) (hc : 0<c) : 0 < (c^n)⁻¹ := inv_pos.mpr (pow_pos hc n)
  have E : (((b^n)⁻¹*((2*a)^n)⁻¹)⁻¹ * (((2*a)^n)⁻¹)^((s-1)/s)) =
      ((diagonalYoungFactor s)^n)^(1/s) := by
    apply Real.log_injOn_pos
    · apply Set.mem_Ioi.mpr; positivity
    · apply Set.mem_Ioi.mpr; positivity
    dsimp [diagonalYoungFactor,a,b,youngFrameA,youngFrameB]
    simp (disch := positivity) only [Real.log_rpow,Real.log_inv,Real.log_pow,Real.log_mul,
      Real.log_div,Real.log_sqrt,Real.log_one]
    field_simp
    ring
  rw [youngDilation,youngDilation,← ENNReal.ofReal_mul (hdil b hb).le,← ENNReal.ofReal_inv_of_pos (mul_pos (hdil b hb) (hdil (2*a) h2a)),
    ENNReal.ofReal_rpow_of_pos (hdil (2*a) h2a),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow hfac.le,ENNReal.ofReal_rpow_of_pos (pow_pos hfac n),E]

end LpGowers
