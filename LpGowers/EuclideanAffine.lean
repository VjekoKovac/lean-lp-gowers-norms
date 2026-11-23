module

public import LpGowers.EuclideanProofs
import LpGowers.DegreeProofs
import LpGowers.Scaling
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Attainment by all Euclidean Gaussians

The proof transports the Gaussian computation from Section 4 of
arXiv:2609.08916v2 along an invertible linear map, a translation and a
positive scalar multiplication. The Gram factorization uses Mathlib's
`CStarAlgebra.nonneg_iff_eq_star_mul_self`. The change of variables uses
`Real.map_matrix_volume_pi_eq_smul_volume_pi`. Haar measure homogeneity
in the base and all increments gives precisely the Lᵠ scaling exponent.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder
namespace LpGowers
noncomputable section

/-- The matrix in the Gaussian definition is a nonsingular real Gram matrix. -/
theorem gaussianQuad_as_squares {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, M i j = M j i) (hp : ∀ v : Rn n, v ≠ 0 → 0 < gaussianQuad M v) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 ∧
      ∀ v, gaussianQuad M v = ∑ i, (B.mulVec v i) ^ 2 := by
  classical
  have hqd (v : Rn n) : gaussianQuad M v = v ⬝ᵥ (M *ᵥ v) := by
    rw [Matrix.dot_mulVec_eq_sum_sum, gaussianQuad, Finset.sum_comm]
  have hM : M.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.ext
      intro i j
      simpa using hs j i
    · intro v hv
      simpa using (hqd v ▸ hp v hv)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hB' : M = B.transpose * B := by simpa [Matrix.star_eq_conjTranspose] using hB
  refine ⟨B, ?_, ?_⟩
  · have hd := hM.det_pos.ne'
    rw [hB', det_mul, det_transpose] at hd
    exact left_ne_zero_of_mul hd
  · intro v
    rw [hqd, hB', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp [dotProduct, pow_two]

theorem cubeProduct_comp_addHom {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    (T : G →+ H) (d : ℕ) (f : H → ℝ≥0) (h : Fin d → G) (x : G) :
    cubeProduct d (fun t => f (T t)) h x =
      cubeProduct d f (fun i => T (h i)) (T x) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [cubeProduct, ih, map_add]; rfl

theorem gowers_comp_addHom {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableAdd₂ H]
    (μ : Measure G) (T : G →+ H) (hT : Measurable T) [SigmaFinite (μ.map T)]
    (d : ℕ) (p : ℝ) (f : H → ℝ≥0) (hf : Measurable f) :
    gowers μ d p (fun t => f (T t)) = gowers (μ.map T) d p f := by
  have R (h : Fin d → G) : autocorrelation μ d (fun t => f (T t)) h =
      autocorrelation (μ.map T) d f (fun i => T (h i)) := by
    unfold autocorrelation
    simp_rw [cubeProduct_comp_addHom]
    exact (lintegral_map (measurable_cubeProduct_comp hf d
      (fun i (_ : H) => T (h i)) (fun _ => measurable_const) id measurable_id) hT).symm
  have mp := Measure.pi_map_pi (μ := fun _ : Fin d => μ)
    (f := fun _ => T) (fun _ => hT.aemeasurable)
  have mT : Measurable (fun x : Fin d → G => fun i => T (x i)) := by fun_prop
  have mR : Measurable (fun y => autocorrelation (μ.map T) d f y ^ p) := by
    have := measurable_autocorrelation (μ.map T) d hf
    fun_prop
  unfold gowers lp cubeMeasure
  simp_rw [R]
  rw [← lintegral_map mR mT, mp]

theorem cubeProduct_translate {G : Type*} [AddCommMonoid G] (d : ℕ)
    (f : G → ℝ≥0) (t : G) (h : Fin d → G) (x : G) :
    cubeProduct d (fun u => f (u + t)) h x = cubeProduct d f h (x + t) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [cubeProduct, ih, add_right_comm]

theorem gowers_translate {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddRightInvariant] (d : ℕ) (p : ℝ)
    (f : G → ℝ≥0) (t : G) : gowers μ d p (fun u => f (u + t)) = gowers μ d p f := by
  have h (z : Fin d → G) : autocorrelation μ d (fun u => f (u+t)) z = autocorrelation μ d f z := by
    unfold autocorrelation
    simp_rw [cubeProduct_translate]
    exact lintegral_add_right_eq_self _ _
  simp only [gowers, lp, h]

/-- The companion input homogeneity for the ordinary Lebesgue functional. -/
theorem lp_smul_liftNN {X : Type*} [MeasurableSpace X] (μ : Measure X) (c : ℝ≥0)
    (f : X → ℝ≥0) (q : ℝ) (hq : 0 < q) :
    lp μ q (liftNN (fun x => c * f x)) = (c : ℝ≥0∞) * lp μ q (liftNN f) := by
  unfold lp liftNN
  simp only [ENNReal.coe_mul, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  simp [hq.ne']

theorem lp_translate {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddRightInvariant] (q : ℝ)
    (f : G → ℝ≥0) (t : G) : lp μ q (liftNN (fun u => f (u + t))) = lp μ q (liftNN f) := by
  unfold lp liftNN
  rw [lintegral_add_right_eq_self (fun u => (f u : ℝ≥0∞)^q) t]

theorem lp_comp_smulMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) (hT : Measurable T) (r : ℝ≥0) (hμ : μ.map T = r • μ)
    (f : X → ℝ≥0) (hf : Measurable f) (q : ℝ) (hq : 0 < q) :
    lp μ q (liftNN (f ∘ T)) = (r : ℝ≥0∞) ^ (1/q) * lp μ q (liftNN f) := by
  have h : Measurable (fun x => (f x : ℝ≥0∞) ^ q) := by fun_prop
  unfold lp liftNN
  simp only [Function.comp_apply]
  rw [← lintegral_map h hT, hμ, lintegral_smul_measure]
  exact ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

/-- Every positive-amplitude Gaussian with arbitrary centre and symmetric
positive-definite quadratic form attains the claimed Euclidean constant. -/
theorem gaussian_equality {n : ℕ} (d : ℕ) (p : ℝ) (hp : 0 < p)
    (g : Rn n → ℝ≥0) (hg : IsEuclideanGaussian g) :
    gowers (euclideanMeasure n) d p g = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN g) := by
  obtain ⟨c, x₀, M, hc, hs, hM, hg⟩ := hg
  obtain ⟨B, hB, hquad⟩ := gaussianQuad_as_squares M hs hM
  let μ := euclideanMeasure n
  let q := criticalExponent d p
  let T : Rn n →+ Rn n := B.toLin'.toAddMonoidHom
  let f := tensorGaussian n 1
  let r : ℝ≥0 := (|(B.det)⁻¹|).toNNReal
  let a : ℝ≥0 := c.toNNReal
  have hμ : μ.map T = r • μ := Real.map_matrix_volume_pi_eq_smul_volume_pi hB
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have : SigmaFinite (μ.map T) := hμ ▸ inferInstance
  have : μ.IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  have hT : Measurable T := LinearMap.continuous_on_pi B.toLin' |>.measurable
  have hf : Measurable f := by unfold f tensorGaussian scalarGaussian; fun_prop
  have hq : 0 < q := by unfold q criticalExponent; positivity
  have hg' : g = fun x => a * (f ∘ T) (x + -x₀) := by
    funext x
    apply NNReal.eq
    rw [hg x, hquad]
    simp only [NNReal.coe_mul, a, Real.coe_toNNReal _ hc.le, f, Function.comp_apply,
      tensorGaussian, NNReal.coe_prod, scalarGaussian, Real.coe_toNNReal _ (Real.exp_nonneg _),
      neg_one_mul, ← Real.exp_sum, Finset.sum_neg_distrib]
    rfl
  have quant : ((d : ℝ) + p) / ((2 : ℝ) ^ d * p) = 1 / q := by
    unfold q criticalExponent
    field_simp
  change gowers μ d p g = _ * lp μ q (liftNN g)
  rw [hg', gowers_smul_input μ a d _ hp, lp_smul_liftNN μ a _ q hq,
    gowers_translate μ, lp_translate μ]
  change (a : ℝ≥0∞) * gowers μ d p (fun x => f (T x)) =
    _ * ((a : ℝ≥0∞) * lp μ q (liftNN (f ∘ T)))
  rw [gowers_comp_addHom μ T hT d p f hf, hμ, gowers_smul_measure μ r d f hp, quant,
    lp_comp_smulMeasure μ T hT r hμ f hf q hq, gaussian_test_equality_scaled d n 1 p one_pos hp]
  ac_rfl

/-- The Gaussian-to-equality direction of the classification in Theorem 1.3(a),
for arbitrary a.e.-equal representatives. -/
theorem ae_gaussian_equality {n : ℕ} (d : ℕ) (p : ℝ) (hp : 0 < p) (f : Rn n → ℝ≥0)
    (h : ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g) :
    gowers (euclideanMeasure n) d p f = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN f) := by
  obtain ⟨g, hg, hfg⟩ := h
  let μ := euclideanMeasure n
  let q := criticalExponent d p
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  have eqR := autocorrelation_congr_ae μ hfg d
  have eqL : lp μ q (liftNN f) = lp μ q (liftNN g) := by
    unfold lp
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    simp only [liftNN, hx]
  change gowers μ d p f = _ * lp μ q (liftNN f)
  rw [eqL]
  convert gaussian_equality d p hp g hg using 1
  unfold gowers
  rw [eqR]

end
end LpGowers
