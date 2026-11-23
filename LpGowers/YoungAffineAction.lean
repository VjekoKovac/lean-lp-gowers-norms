module

public import LpGowers.GaussianAffinePullback
public import LpGowers.EuclideanInverse
import LpGowers.LogMoments
import LpGowers.Normalization
import LpGowers.Scaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-! The affine symmetries of normalized diagonal Young extremizing sequences.
The same determinant factor preserves the critical norm, critical distance,
and the degree-one moment. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers
noncomputable section

/-- An invertible real linear transformation followed by a translation. -/
structure YoungAffine (n : ℕ) where
  linear : Rn n ≃L[ℝ] Rn n
  offset : Rn n

namespace YoungAffine
variable {n : ℕ} (A : YoungAffine n)

def jacobian : ℝ≥0 := |(LinearMap.det A.linear.toLinearEquiv.toLinearMap)⁻¹|.toNNReal

theorem jacobian_pos : 0 < A.jacobian := by
  exact Real.toNNReal_pos.mpr (abs_pos.mpr (inv_ne_zero A.linear.toLinearEquiv.isUnit_det'.ne_zero))

theorem map_linear : (euclideanMeasure n).map A.linear = A.jacobian • euclideanMeasure n := by
  change Measure.map A.linear.toLinearEquiv.toLinearMap volume = _
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar _
    A.linear.toLinearEquiv.isUnit_det'.ne_zero

def amplitude (q : ℝ) : ℝ≥0 := (A.jacobian ^ (1/q))⁻¹

theorem amplitude_pos (q : ℝ) : 0 < A.amplitude q :=
  inv_pos.mpr (NNReal.rpow_pos A.jacobian_pos)

theorem cancel_amplitude (q : ℝ) :
    (A.amplitude q : ℝ≥0∞) * (A.jacobian : ℝ≥0∞)^(1/q) = 1 := by
  rw [← ENNReal.coe_rpow_of_ne_zero A.jacobian_pos.ne', ← ENNReal.coe_mul]
  exact congrArg (fun v : ℝ≥0 => (v : ℝ≥0∞)) (inv_mul_cancel₀ (NNReal.rpow_pos A.jacobian_pos : 0 < A.jacobian^(1/q)).ne')

def act (q : ℝ) (f : Rn n → ℝ≥0) (x : Rn n) : ℝ≥0 :=
  A.amplitude q * f (A.linear x + A.offset)

theorem quasiMeasurePreserving :
    MeasureTheory.QuasiMeasurePreserving (fun x => A.linear x + A.offset)
      (euclideanMeasure n) (euclideanMeasure n) := by
  have hl : MeasureTheory.QuasiMeasurePreserving A.linear (euclideanMeasure n) (euclideanMeasure n) :=
    ⟨A.linear.continuous.measurable.aemeasurable, A.map_linear ▸ Measure.smul_absolutelyContinuous⟩
  exact (measurePreserving_add_right (volume : Measure (Rn n)) A.offset).quasiMeasurePreserving.comp hl

theorem aemeasurable {f : Rn n → ℝ≥0} (hf : AEMeasurable f (euclideanMeasure n)) (q : ℝ) :
    AEMeasurable (A.act q f) (euclideanMeasure n) :=
  aemeasurable_const.mul (hf.comp_quasiMeasurePreserving A.quasiMeasurePreserving)

theorem lintegral_comp (W : Rn n → ℝ≥0∞) :
    (∫⁻ x, W (A.linear x + A.offset) ∂euclideanMeasure n) =
      (A.jacobian : ℝ≥0∞) * ∫⁻ x, W x ∂euclideanMeasure n := by
  have : (euclideanMeasure n).IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  have emb : MeasurableEmbedding A.linear := A.linear.toHomeomorph.measurableEmbedding
  rw [← emb.lintegral_map (fun x => W (x+A.offset)), A.map_linear, lintegral_smul_measure,
    lintegral_add_right_eq_self]
  rfl

theorem lp_comp (W : Rn n → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    lp (euclideanMeasure n) q (fun x => W (A.linear x+A.offset)) =
      (A.jacobian : ℝ≥0∞)^(1/q) * lp (euclideanMeasure n) q W := by
  unfold lp
  rw [A.lintegral_comp (fun x => W x ^ q), ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

theorem mass_act (f : Rn n → ℝ≥0) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, (A.act q f x : ℝ≥0∞)^q ∂euclideanMeasure n) =
      ∫⁻ x, (f x : ℝ≥0∞)^q ∂euclideanMeasure n := by
  have h := lp_smul_liftNN (euclideanMeasure n) (A.amplitude q)
    (fun x => f (A.linear x+A.offset)) q hq
  rw [show liftNN (fun x => f (A.linear x+A.offset)) =
    (fun x => liftNN f (A.linear x+A.offset)) from rfl,
    A.lp_comp _ hq, ← mul_assoc, A.cancel_amplitude, one_mul] at h
  have H := congrArg (fun z : ℝ≥0∞ => z^q) h
  simpa [act, lp, liftNN, ← ENNReal.rpow_mul, hq.ne'] using H

theorem distance_act (f g : Rn n → ℝ≥0) {q : ℝ} (hq : 0 < q) :
    lpDist (euclideanMeasure n) q (A.act q f) (A.act q g) =
      lpDist (euclideanMeasure n) q f g := by
  unfold act
  rw [lpDist_smul_input _ _ _ _ hq]
  unfold lpDist
  rw [A.lp_comp (fun x => edist (f x) (g x)) hq, ← mul_assoc, A.cancel_amplitude, one_mul]

theorem moment_act {s : ℝ} (hs : 0 < s) {f : Rn n → ℝ≥0}
    (hf : AEMeasurable f (euclideanMeasure n)) :
    cubeMoment 1 n s (A.act (criticalExponent 1 s) f) = cubeMoment 1 n s f := by
  let μ := euclideanMeasure n
  let q := criticalExponent 1 s
  let T : Rn n →+ Rn n := A.linear.toLinearEquiv.toAddMonoidHom
  have hT : Measurable T := A.linear.continuous.measurable
  have hμ : μ.map T = A.jacobian • μ := A.map_linear
  have : SigmaFinite μ := by change SigmaFinite (volume : Measure (Rn n)); infer_instance
  have : SigmaFinite (μ.map T) := hμ ▸ inferInstance
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  have : μ.IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  have transM : Measurable (fun x => hf.mk f (x+A.offset)) :=
    hf.measurable_mk.comp (measurable_id.add_const _)
  have quant : (((1:ℕ):ℝ)+s)/((2:ℝ)^1*s) = 1/q := by
    simp [q, criticalExponent, div_div_eq_mul_div]
  have hEq : A.act q f =ᵐ[μ] A.act q (hf.mk f) :=
    Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) (A.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk)
  have hG : gowers μ 1 s (A.act q f) = gowers μ 1 s f := by
    rw [show gowers μ 1 s (A.act q f) = gowers μ 1 s (A.act q (hf.mk f)) from
      congrArg (fun R => (lp (cubeMeasure μ 1) s R)^(1/(2:ℝ)^1)) (autocorrelation_congr_ae μ hEq 1)]
    unfold act
    rw [gowers_smul_input μ _ _ _ hs]
    change (A.amplitude q : ℝ≥0∞) * gowers μ 1 s (fun x => hf.mk f (T x + A.offset)) = _
    rw [gowers_comp_addHom μ T hT 1 s _ transM, hμ,
      gowers_smul_measure μ _ 1 _ hs, gowers_translate, quant, ← mul_assoc, A.cancel_amplitude, one_mul]
    unfold gowers
    rw [autocorrelation_congr_ae μ hf.ae_eq_mk 1]
  exact (gowers_moment_power μ 1 hs _).symm.trans
    ((congrArg (fun z : ℝ≥0∞ => z^((2:ℝ)^1*s)) hG).trans (gowers_moment_power μ 1 hs f))

/-- Pull a Gaussian in transformed coordinates back to the original coordinates. -/
theorem pullback_gaussian {q : ℝ} {g : Rn n → ℝ≥0} (hg : IsEuclideanGaussian g) :
    ∃ v : Rn n → ℝ≥0, IsEuclideanGaussian v ∧ A.act q v = g := by
  let v := fun x => (A.amplitude q)⁻¹ * g (A.linear.symm x + -(A.linear.symm A.offset))
  refine ⟨v, gaussian_affine_pullback hg _ _ _ (inv_pos.mpr (A.amplitude_pos q)), ?_⟩
  funext x
  simp [v, act, (A.amplitude_pos q).ne']

end YoungAffine
end
end LpGowers
