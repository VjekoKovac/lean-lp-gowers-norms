module

public import LpGowers.EuclideanProofs
import LpGowers.DegreeProofs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-!
# The sharp Young reduction for the Euclidean inequality

Section 4 of arXiv:2609.08916v2 iterates the sharp Young inequality of
Beckner. We expose just the autocorrelation case of that classical input,
then prove the recurrence, its iteration, and the displayed estimate
including its constant. `SharpDiagonalYoung` is a proposition taken as a
hypothesis of the reduction.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LpGowers

noncomputable section

/-- The one-step Beckner constant raised to the exponent `p`, in one
dimension. The factor in `n` dimensions is its `n`th power. -/
def diagonalYoungFactor (p : ℝ) : ℝ := 2 * p ^ (p / 2) / (p+1) ^ ((p+1)/2)

/-- Beckner's sharp Young inequality, restricted to an autocorrelation and
raised to the `p`th power. This proposition is an explicit external input
in the reduction below. -/
def SharpDiagonalYoung (n : ℕ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∀ F : Rn n → ℝ≥0, Measurable F →
    let μ := euclideanMeasure n
    (∫⁻ t, (∫⁻ x, (F x : ℝ≥0∞) * F (x+t) ∂μ) ^ p ∂μ) ≤
      (ENNReal.ofReal (diagonalYoungFactor p)) ^ n *
      (∫⁻ x, (F x : ℝ≥0∞) ^ (2*p/(p+1)) ∂μ) ^ (p+1)

private theorem cubeProduct_finite {G : Type*} [AddCommMonoid G]
    (d : ℕ) (f : G → ℝ≥0) (h : Fin d → G) (x : G) : cubeProduct d f h x ≠ ⊤ := by
  induction d generalizing x with
  | zero => exact ENNReal.coe_ne_top
  | succ d ih => exact ENNReal.mul_ne_top (ih _ _) (ih _ _)

private theorem cubeProduct_rpow {G : Type*} [AddCommMonoid G] (d : ℕ) (f : G → ℝ≥0)
    (h : Fin d → G) (x : G) {p : ℝ} (hp : 0 ≤ p) :
    cubeProduct d (fun y => (f y)^p) h x = (cubeProduct d f h x)^p := by
  induction d generalizing x with
  | zero => exact ENNReal.coe_rpow_of_nonneg _ hp
  | succ d ih => simp only [cubeProduct, ih, ENNReal.mul_rpow_of_nonneg _ _ hp]

/-- The source recurrence before taking roots. Only the sharp Young step
is assumed. -/
theorem euclidean_young_recurrence {n : ℕ} (hY : SharpDiagonalYoung n)
    (d : ℕ) (p : ℝ) (hp : 1 ≤ p) (f : Rn n → ℝ≥0) (hf : Measurable f) :
    let μ := euclideanMeasure n
    (∫⁻ h, (autocorrelation μ (d+1) f h)^p ∂cubeMeasure μ (d+1)) ≤
      (ENNReal.ofReal (diagonalYoungFactor p))^n * ∫⁻ h,
        (autocorrelation μ d (fun x => (f x)^(2*p/(p+1))) h)^(p+1) ∂cubeMeasure μ d := by
  let μ := euclideanMeasure n
  let r := 2*p/(p+1)
  have hr : 0 ≤ r := by unfold r; positivity
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have : SigmaFinite (cubeMeasure μ d) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => Rn n) 0
  have he : MeasurePreserving e (cubeMeasure μ (d+1)) (μ.prod (cubeMeasure μ d)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  let V := fun h => (autocorrelation μ (d+1) f h)^p
  have hV : Measurable V := (measurable_autocorrelation μ (d+1) hf).pow_const p
  change (∫⁻ h, V h ∂cubeMeasure μ (d+1)) ≤ _
  rw [← ((MeasurePreserving.symm e he).lintegral_comp hV),
    lintegral_prod_symm' (fun z => V (e.symm z)) (hV.comp e.symm.measurable),
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro h
  let F : Rn n → ℝ≥0 := fun x => (cubeProduct d f h x).toNNReal
  have hF : Measurable F := (measurable_cubeProduct_comp hf d
    (fun i (_ : Rn n) => h i) (fun _ => measurable_const) id measurable_id).ennreal_toNNReal
  have hco (x : Rn n) : (F x : ℝ≥0∞) = cubeProduct d f h x :=
    ENNReal.coe_toNNReal (cubeProduct_finite d f h x)
  have hy := hY p hp F hF
  simp only [hco] at hy
  have split (t x : Rn n) : cubeProduct (d+1) f (e.symm (t,h)) x =
      cubeProduct d f h x * cubeProduct d f h (x+t) := cubeProduct_insertNth d f 0 t h x
  unfold V autocorrelation
  simpa only [split, cubeProduct_rpow d f h _ (show 0 ≤ 2*p/(p+1) from hr)] using hy

/-- The product of the simplified Young factors after `d` iterations. -/
def iteratedYoungFactor (d : ℕ) (p : ℝ) :=
  (2 : ℝ)^d * p^(p/2) / (p+d)^((p+d)/2)

theorem youngFactor_rec (d : ℕ) (p : ℝ) (hp : 0 < p) :
    diagonalYoungFactor p * iteratedYoungFactor d (p+1) = iteratedYoungFactor (d+1) p := by
  unfold diagonalYoungFactor iteratedYoungFactor
  have eq : p + 1 + (d : ℝ) = p + (d+1 : ℕ) := by push_cast; ring
  rw [eq, pow_succ]
  field_simp [(Real.rpow_pos_of_pos (show 0 < p+1 by positivity) _).ne']


theorem euclidean_iterated_young {n : ℕ} (hY : SharpDiagonalYoung n)
    (d : ℕ) (p : ℝ) (hp : 1 ≤ p) (f : Rn n → ℝ≥0) (hf : Measurable f) :
    let μ := euclideanMeasure n
    (∫⁻ h, (autocorrelation μ d f h) ^ p ∂cubeMeasure μ d) ≤
      ENNReal.ofReal (iteratedYoungFactor d p) ^ n *
      (∫⁻ x, (f x : ℝ≥0∞)^(criticalExponent d p) ∂μ) ^ ((d : ℝ)+p) := by
  let μ := euclideanMeasure n
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  induction d generalizing p f with
  | zero =>
      have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
      simp [autocorrelation, cubeProduct, cubeMeasure, iteratedYoungFactor, criticalExponent, hp'.ne',
        div_self (Real.rpow_pos_of_pos hp' _).ne']
  | succ d ih =>
      let r := 2*p/(p+1)
      have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have hr : 0 < r := by unfold r; positivity
      have hp1 : 1 ≤ p+1 := by linarith
      have hf' : Measurable (fun x => (f x)^r) := hf.pow_const r
      have H := ih (p+1) hp1 _ hf'
      have hq : r * criticalExponent d (p+1) = criticalExponent (d+1) p := by
        unfold r criticalExponent
        push_cast
        rw [pow_succ]
        field_simp
        ring
      have hsum : (d : ℝ) + (p + 1) = (d + 1 : ℕ) + p := by push_cast; ring
      simp only [ENNReal.coe_rpow_of_nonneg _ hr.le, ← ENNReal.rpow_mul, hq, hsum] at H
      refine (euclidean_young_recurrence hY d p hp f hf).trans ?_
      refine (mul_le_mul_right H (ENNReal.ofReal (diagonalYoungFactor p) ^ n)).trans_eq ?_
      rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul (show 0 ≤ diagonalYoungFactor p by
        unfold diagonalYoungFactor; positivity), youngFactor_rec d p hp']

theorem iteratedFactor_root (d n : ℕ) (p : ℝ) (hp : 0 < p) :
    ((ENNReal.ofReal (iteratedYoungFactor d p))^n) ^ (1 / p * (1 / (2 : ℝ)^d)) =
      ENNReal.ofReal (sharpEuclideanConstant d n p) := by
  unfold iteratedYoungFactor sharpEuclideanConstant
  simp (disch := positivity) only [← ENNReal.ofReal_pow, ENNReal.ofReal_rpow_of_pos]
  apply congrArg ENNReal.ofReal
  apply Real.log_injOn_pos
  · apply Set.mem_Ioi.mpr; positivity
  · apply Set.mem_Ioi.mpr; positivity
  simp (disch := positivity) only [Real.log_rpow, Real.log_mul, Real.log_div, Real.log_pow,
    Nat.cast_mul, Nat.cast_ofNat, pow_succ, add_comm p]
  field_simp

/-- The entire all-functions inequality in Theorem 1.3(a) follows from
Beckner's diagonal Young inequality, with the displayed sharp factor. -/
theorem euclideanBound_of_sharpDiagonalYoung {n : ℕ} (hY : SharpDiagonalYoung n)
    (d : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    EuclideanBound d n p (ENNReal.ofReal (sharpEuclideanConstant d n p)) := by
  intro f hf
  let μ := euclideanMeasure n
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  let F := hf.mk f
  have hfg : f =ᵐ[μ] F := hf.ae_eq_mk
  have eqR := autocorrelation_congr_ae μ hfg d
  have eqI : (∫⁻ x, (f x : ℝ≥0∞)^(criticalExponent d p) ∂μ) =
      ∫⁻ x, (F x : ℝ≥0∞)^(criticalExponent d p) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have he : ((d : ℝ)+p) * (1 / p * (1 / (2 : ℝ)^d)) = 1 / criticalExponent d p := by
    unfold criticalExponent
    field_simp
  change gowers μ d p f ≤ _ * lp μ (criticalExponent d p) (liftNN f)
  unfold gowers lp liftNN
  rw [eqR, eqI, ← ENNReal.rpow_mul]
  refine (ENNReal.rpow_le_rpow (euclidean_iterated_young hY d p hp F hf.measurable_mk)
    (by positivity)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), iteratedFactor_root d n p hp',
    ← ENNReal.rpow_mul, he]

end
end LpGowers
