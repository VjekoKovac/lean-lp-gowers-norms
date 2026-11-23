module

public import LpGowers.Euclidean
public import LpGowers.ProductIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Steps in the proof of the sharp Euclidean bound

The product below is the simplified product of Beckner constants in §4 of
Kovač–Rogers. The Gaussian calculation uses Mathlib's
`integrable_exp_neg_mul_sq` and `integral_gaussian`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LpGowers

noncomputable section

/-- Telescoping product in the iteration of the sharp Young estimate. -/
theorem youngConstantProduct (d : ℕ) (p : ℝ) (hp : 0 < p) :
    (∏ j ∈ Finset.range d,
      2 * (p + j) ^ ((p + j) / 2) / (p + (j + 1 : ℕ)) ^ ((p + (j + 1 : ℕ)) / 2)) =
      (2 : ℝ) ^ d * p ^ (p / 2) / (p + d) ^ ((p + d) / 2) := by
  induction d with
  | zero =>
      simp [div_self (Real.rpow_pos_of_pos hp _).ne']
  | succ d ih =>
      rw [Finset.prod_range_succ, ih, pow_succ]
      have hd : 0 < p + (d : ℝ) := by positivity
      have hd' : 0 < p + ((d + 1 : ℕ) : ℝ) := by positivity
      field_simp [(Real.rpow_pos_of_pos hd _).ne', (Real.rpow_pos_of_pos hd' _).ne']

/-- Gaussian test function on the real line with parameter `a`. -/
def scalarGaussian (a x : ℝ) : ℝ≥0 := (Real.exp (-a * x ^ 2)).toNNReal

/-- Completing the square simultaneously over all vertices of the scalar cube.
The shifts and the base point are arbitrary, including coincident vertices. -/
theorem cubeProduct_scalarGaussian (a : ℝ) (d : ℕ) (h : Fin d → ℝ) (x : ℝ) :
    cubeProduct d (scalarGaussian a) h x =
      ENNReal.ofReal (Real.exp (-(a * 2 ^ d) *
        ((x + (∑ i, h i) / 2) ^ 2 + (∑ i, h i ^ 2) / 4))) := by
  induction d generalizing x with
  | zero => simp [cubeProduct, scalarGaussian, ENNReal.ofReal]
  | succ d ih =>
      rw [cubeProduct, ih, ih, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply congrArg ENNReal.ofReal
      apply congrArg Real.exp
      simp only [Fin.sum_univ_succ, Fin.tail, pow_succ]
      ring

/-- Integral of a translated scalar Gaussian, in the extended nonnegative
normalisation used for the multiple autocorrelation. -/
theorem lintegral_shiftedGaussian (b s : ℝ) (hb : 0 < b) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-b * (x + s) ^ 2))) =
      ENNReal.ofReal (Real.sqrt (Real.pi / b)) := by
  rw [lintegral_add_right_eq_self
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-b * x ^ 2))) s]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hb)
    (Filter.Eventually.of_forall fun x => (Real.exp_nonneg _)), integral_gaussian]

/-- Exact one-dimensional Gaussian multiple autocorrelation. For `a = π` this
is the Gaussian test in the sharpness proof of Theorem 1.3(a) with `n = 1`. -/
theorem autocorrelation_scalarGaussian (a : ℝ) (ha : 0 < a) (d : ℕ) (h : Fin d → ℝ) :
    autocorrelation volume d (scalarGaussian a) h =
      ENNReal.ofReal (Real.exp (-(a * 2 ^ d) * ((∑ i, h i ^ 2) / 4))) *
      ENNReal.ofReal (Real.sqrt (Real.pi / (a * 2 ^ d))) := by
  unfold autocorrelation
  simp_rw [cubeProduct_scalarGaussian]
  have split (x : ℝ) :
      -(a * 2 ^ d) * ((x + (∑ i, h i) / 2) ^ 2 + (∑ i, h i ^ 2) / 4) =
      -(a * 2 ^ d) * ((∑ i, h i ^ 2) / 4) +
      -(a * 2 ^ d) * (x + (∑ i, h i) / 2) ^ 2 := by ring
  simp_rw [split, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_shiftedGaussian _ _ (by positivity)]

/-- A coordinatewise product remains a product after forming the cube. -/
theorem cubeProduct_tensor {G : Type*} [AddCommMonoid G] (d n : ℕ)
    (f : Fin n → G → ℝ≥0) (h : Fin d → Fin n → G) (x : Fin n → G) :
    cubeProduct d (fun y : Fin n → G => ∏ k, f k (y k)) h x =
      ∏ k, cubeProduct d (f k) (fun i => h i k) (x k) := by
  induction d generalizing x with
  | zero => simp [cubeProduct]
  | succ d ih =>
      simp only [cubeProduct, ih, Finset.prod_mul_distrib]
      rfl

/-- Gaussian on ℝⁿ as a product of the `n` scalar factors. -/
def tensorGaussian (n : ℕ) (a : ℝ) (x : Rn n) : ℝ≥0 := ∏ k, scalarGaussian a (x k)

/-- The full n-dimensional autocorrelation of the Gaussian test from §4,
written as a product of its exact one-dimensional factors. -/
theorem autocorrelation_tensorGaussian (d n : ℕ) (a : ℝ) (ha : 0 < a)
    (h : Fin d → Rn n) :
    autocorrelation (euclideanMeasure n) d (tensorGaussian n a) h =
      ∏ k : Fin n, ENNReal.ofReal (Real.exp (-(a * 2 ^ d) * ((∑ i, (h i k) ^ 2) / 4))) *
        ENNReal.ofReal (Real.sqrt (Real.pi / (a * 2 ^ d))) := by
  change (∫⁻ x : Rn n, cubeProduct d (fun y : Rn n => ∏ k, scalarGaussian a (y k)) h x
    ∂cubeMeasure volume n) = _
  simp_rw [cubeProduct_tensor]
  have hm (k : Fin n) : Measurable (fun t : ℝ =>
      cubeProduct d (scalarGaussian a) (fun i => h i k) t) := by
    simp_rw [cubeProduct_scalarGaussian]
    fun_prop
  rw [lintegral_pi_separated volume n _ hm]
  exact Finset.prod_congr rfl fun k _ => autocorrelation_scalarGaussian a ha d (fun i => h i k)

/-- Extended Gaussian factors, and their one-coordinate integrals. -/
def gaussianFactor (a x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a * x ^ 2))
def gaussianMass (a : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (Real.pi / a))

theorem gaussianFactor_rpow (a x p : ℝ) :
    gaussianFactor a x ^ p = gaussianFactor (a * p) x := by
  unfold gaussianFactor
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  ring

theorem lintegral_tensorGaussian (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫⁻ x : Rn n, ∏ k, gaussianFactor a (x k) ∂euclideanMeasure n) = gaussianMass a ^ n := by
  change (∫⁻ x : Rn n, ∏ k, gaussianFactor a (x k) ∂cubeMeasure volume n) = _
  have h (i : Fin n) : Measurable (gaussianFactor a) := by unfold gaussianFactor; fun_prop
  rw [lintegral_pi_separated volume n (fun _ => gaussianFactor a) h]
  have h' : (∫⁻ x : ℝ, gaussianFactor a x) = gaussianMass a := by
    simpa [gaussianMass, gaussianFactor] using lintegral_shiftedGaussian a 0 ha
  simp [h']

theorem lp_tensorGaussian (n : ℕ) (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    lp (euclideanMeasure n) p (liftNN (tensorGaussian n a)) =
      (gaussianMass (a * p) ^ n) ^ (1 / p) := by
  unfold lp
  have lift (x : Rn n) : liftNN (tensorGaussian n a) x = ∏ k, gaussianFactor a (x k) := by
    simp [liftNN, tensorGaussian, scalarGaussian, gaussianFactor, ENNReal.ofReal]
  simp_rw [lift, ← ENNReal.prod_rpow_of_nonneg hp.le, gaussianFactor_rpow]
  rw [lintegral_tensorGaussian n _ (mul_pos ha hp)]

theorem autocorrelation_tensorGaussian_factored (d n : ℕ) (a : ℝ) (ha : 0 < a)
    (h : Fin d → Rn n) :
    autocorrelation (euclideanMeasure n) d (tensorGaussian n a) h =
      gaussianMass (a * 2 ^ d) ^ n *
      ∏ i, ∏ k, gaussianFactor (a * 2 ^ d / 4) (h i k) := by
  rw [autocorrelation_tensorGaussian d n a ha h]
  have he (k : Fin n) :
      ENNReal.ofReal (Real.exp (-(a * 2 ^ d) * ((∑ i, (h i k) ^ 2) / 4))) =
      ∏ i, gaussianFactor (a * 2 ^ d / 4) (h i k) := by
    unfold gaussianFactor
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum,
      ← Finset.mul_sum]
    congr 2
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp [gaussianMass, mul_comm]

/-- Evaluation of the Gowers-type functional on the Gaussian test for all
dimensions, degrees, and positive finite real exponents. -/
theorem gowers_tensorGaussian (d n : ℕ) (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    gowers (euclideanMeasure n) d p (tensorGaussian n a) =
      (((gaussianMass (a * 2 ^ d) ^ n) ^ p *
        (gaussianMass ((a * 2 ^ d / 4) * p) ^ n) ^ d) ^ (1 / p)) ^ (1 / (2 : ℝ) ^ d) := by
  unfold gowers lp
  simp_rw [autocorrelation_tensorGaussian_factored d n a ha,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.prod_rpow_of_nonneg hp.le, gaussianFactor_rpow]
  have hb : 0 < (a * 2 ^ d / 4) * p := by positivity
  let b := (a * 2 ^ d / 4) * p
  let F : Rn n → ℝ≥0∞ := fun x => ∏ k, gaussianFactor b (x k)
  have hm : Measurable F := by unfold F gaussianFactor; fun_prop
  have hfin : ((gaussianMass (a * 2 ^ d) ^ n) ^ p) ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg hp.le (ENNReal.pow_ne_top (by exact ENNReal.ofReal_ne_top))
  rw [lintegral_const_mul' _ _ hfin]
  have : SigmaFinite (euclideanMeasure n) := by unfold euclideanMeasure; infer_instance
  have hprod := lintegral_pi_separated (euclideanMeasure n) d (fun _ => F) (fun _ => hm)
  rw [hprod]
  change ((_ * ∏ _ : Fin d, ∫⁻ x : Rn n, ∏ k, gaussianFactor b (x k) ∂euclideanMeasure n) ^ _) ^ _ = _
  simp [lintegral_tensorGaussian n b hb, b]

/-- The test functions really belong to the Gaussian family in the statement. -/
theorem isEuclideanGaussian_tensorGaussian (n : ℕ) (a : ℝ) (ha : 0 < a) :
    IsEuclideanGaussian (tensorGaussian n a) := by
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then a else 0
  have quad (v : Rn n) : gaussianQuad M v = a * ∑ i, (v i) ^ 2 := by
    simp [gaussianQuad, M, mul_ite, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]
  refine ⟨1, 0, M, zero_lt_one, ?_, ?_, ?_⟩
  · intro i j
    simp only [M, eq_comm]
  · intro v hv
    rw [quad]
    apply mul_pos ha
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    exact Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  · intro x
    simp only [tensorGaussian, scalarGaussian, NNReal.coe_prod, Real.coe_toNNReal _ (Real.exp_nonneg _),
      sub_zero, one_mul, quad, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]


/-- The sharp constant is attained by every centred isotropic Gaussian in every
dimension and at every positive finite exponent. -/
theorem gaussian_test_equality_scaled (d n : ℕ) (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    gowers (euclideanMeasure n) d p (tensorGaussian n a) =
      ENNReal.ofReal (sharpEuclideanConstant d n p) *
        lp (euclideanMeasure n) (criticalExponent d p) (liftNN (tensorGaussian n a)) := by
  have hq : 0 < criticalExponent d p := by unfold criticalExponent; positivity
  rw [gowers_tensorGaussian d n a p ha hp,
    lp_tensorGaussian n a _ ha hq]
  unfold gaussianMass criticalExponent sharpEuclideanConstant
  simp (disch := positivity) only [← ENNReal.ofReal_pow, ENNReal.ofReal_rpow_of_pos,
    ← ENNReal.ofReal_mul]
  apply congrArg ENNReal.ofReal
  apply Real.log_injOn_pos
  · apply Set.mem_Ioi.mpr
    positivity
  · apply Set.mem_Ioi.mpr
    positivity
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow (2 : ℝ) 2
  simp (disch := positivity) only [Real.log_rpow, Real.log_mul, Real.log_pow, Real.log_sqrt,
    Real.log_div, h4, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

/-- The sharp constant is attained by the source's test Gaussian in every
dimension and at every positive finite exponent. -/
theorem gaussian_test_equality (d n : ℕ) (p : ℝ) (hp : 0 < p) :
    gowers (euclideanMeasure n) d p (tensorGaussian n Real.pi) =
      ENNReal.ofReal (sharpEuclideanConstant d n p) *
        lp (euclideanMeasure n) (criticalExponent d p) (liftNN (tensorGaussian n Real.pi)) :=
  gaussian_test_equality_scaled d n Real.pi p Real.pi_pos hp

/-- Every admissible Euclidean bound is at least the constant in Theorem 1.3(a). -/
theorem euclideanConstant_le_of_bound (d n : ℕ) (p : ℝ) (hp : 0 < p)
    (k : ℝ≥0∞) (hk : EuclideanBound d n p k) :
    ENNReal.ofReal (sharpEuclideanConstant d n p) ≤ k := by
  let q := criticalExponent d p
  have hq : 0 < q := by unfold q criticalExponent; positivity
  have hf : Measurable (tensorGaussian n Real.pi) := by
    unfold tensorGaussian scalarGaussian
    fun_prop
  have h := hk (tensorGaussian n Real.pi) hf.aemeasurable
  rw [gaussian_test_equality d n p hp] at h
  rw [lp_tensorGaussian n _ _ Real.pi_pos hq] at h
  have hr : 0 < Real.sqrt (Real.pi / (Real.pi * q)) := by positivity
  have hx : (gaussianMass (Real.pi * q) ^ n) ^ (1 / q) ≠ 0 := by
    unfold gaussianMass
    positivity
  have hy : (gaussianMass (Real.pi * q) ^ n) ^ (1 / q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  exact (ENNReal.mul_le_mul_iff_left hx hy).mp h

end
end LpGowers
