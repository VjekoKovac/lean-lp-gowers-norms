module

public import LpGowers.YoungAffineAction
public import LpGowers.YoungHeatPath
public import LpGowers.GeometricYoung
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-! # The unit Gaussian orbit and the Gaussian heat profile -/
@[expose] public section
noncomputable section
open MeasureTheory GeometricBrascampLieb
open scoped NNReal ENNReal BigOperators
namespace LpGowers

private lemma quadratic_gaussian_coordinates {n : ℕ} {g : Rn n → ℝ≥0}
    (hg : IsEuclideanGaussian g) :
    ∃ (a : ℝ) (b : Rn n) (B : Rn n ≃L[ℝ] Rn n), 0 < a ∧
      ∀ x, (g x : ℝ) = a * Real.exp (-(∑ i, (B (x-b) i)^2)) := by
  obtain ⟨a,b,M,ha,hs,hp,hg⟩ := hg
  obtain ⟨P,hP,hQ⟩ := gaussianQuad_as_squares M hs hp
  let I := P.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hP)
  let B := (P.toLinearEquiv' I).toContinuousLinearEquiv
  refine ⟨a,b,B,ha,?_⟩
  intro x
  rw [hg,hQ]
  rfl

/-- The mass-preserving affine action is transitive on unit Gaussians at
every positive critical exponent. The equality is pointwise. -/
theorem normalized_gaussian_orbit {n : ℕ} {q : ℝ} (hq : 0 < q)
    {f g : Rn n → ℝ≥0} (hf : IsEuclideanGaussian f) (hg : IsEuclideanGaussian g)
    (hfm : (∫⁻ x, (f x : ℝ≥0∞)^q ∂euclideanMeasure n) = 1)
    (hgm : (∫⁻ x, (g x : ℝ≥0∞)^q ∂euclideanMeasure n) = 1) :
    ∃ A : YoungAffine n, A.act q f = g := by
  obtain ⟨a,b,B,ha,hf⟩ := quadratic_gaussian_coordinates hf
  obtain ⟨c,d,D,hc,hg⟩ := quadratic_gaussian_coordinates hg
  let T := D.trans B.symm
  let A : YoungAffine n := ⟨T, b-T d⟩
  let r : ℝ≥0 := ((A.amplitude q : ℝ)*a/c).toNNReal
  have hrc : (r:ℝ) = (A.amplitude q:ℝ)*a/c := Real.coe_toNNReal _ (by positivity)
  have hrel : A.act q f = fun x => r * g x := by
    funext x
    apply NNReal.eq
    change ((A.amplitude q * f (T x+(b-T d)) : ℝ≥0):ℝ) = _
    rw [NNReal.coe_mul,NNReal.coe_mul,hrc,hf,hg]
    have he : B (T x+(b-T d)-b) = D (x-d) := by
      rw [show T x+(b-T d)-b = T (x-d) by rw [map_sub]; abel]
      exact B.apply_symm_apply _
    rw [he]
    field_simp
  have hN := A.mass_act f hq
  rw [hrel,hfm] at hN
  simp only [ENNReal.coe_mul,ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top),
    hgm,mul_one] at hN
  have hroot := congrArg (fun z : ℝ≥0∞ => z^(1/q)) hN
  have hr : (r:ℝ≥0∞) = 1 := by
    simpa only [← ENNReal.rpow_mul,mul_one_div_cancel hq.ne',ENNReal.rpow_one,ENNReal.one_rpow] using hroot
  have hr' : r=1 := by exact_mod_cast hr
  exact ⟨A,by simpa [hr'] using hrel⟩

/-- Gaussian whose q-th power is the unit-mass heat kernel in Hilbert coordinates. -/
def rootedHeatGaussian (n : ℕ) (q t : ℝ) (x : Rn n) : ℝ≥0 :=
  (heatGaussian (YoungHilbert n) t (WithLp.toLp 2 x)).toNNReal ^ (1/q)

theorem rootedHeatGaussian_formula (n : ℕ) {q t : ℝ} (_hq : 0 < q) (_ht : 0 < t) (x : Rn n) :
    (rootedHeatGaussian n q t x : ℝ) =
      (heatNormalization (E := YoungHilbert n) t)^(1/q) *
      Real.exp (-((4*t)⁻¹/q) * ∑ i, x i ^ 2) := by
  have hn : 0 < heatNormalization (E := YoungHilbert n) t := Real.exp_pos _
  rw [rootedHeatGaussian, NNReal.coe_rpow, Real.coe_toNNReal _ (by
    exact mul_nonneg hn.le (Real.exp_pos _).le), heatGaussian,
    Real.mul_rpow hn.le (Real.exp_pos _).le, ← Real.exp_mul, EuclideanSpace.real_norm_sq_eq]
  congr 2
  change (-(4*t)⁻¹ * (∑ i, x i^2)) * (1/q) = _
  ring

theorem rootedHeatGaussian_isGaussian (n : ℕ) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    IsEuclideanGaussian (rootedHeatGaussian n q t) := by
  let w := (4*t)⁻¹/q
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => if i=j then w else 0
  have hw : 0 < w := by dsimp [w]; positivity
  have hQ (v : Rn n) : gaussianQuad M v = w * ∑ i, v i^2 := by
    simp [gaussianQuad,M,mul_ite,Finset.mul_sum,pow_two,mul_comm,mul_left_comm,mul_assoc]
  refine ⟨(heatNormalization (E := YoungHilbert n) t)^(1/q),0,M,Real.rpow_pos_of_pos (Real.exp_pos _) (1/q),?_,?_,?_⟩
  · intro i j; simp [M,eq_comm]
  · intro v hv
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      contrapose! hv; funext i; exact hv i
    rw [hQ]
    exact mul_pos hw (Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩)
  · intro x
    simpa [hQ,w,neg_mul] using rootedHeatGaussian_formula n hq ht x

theorem rootedHeatGaussian_mass (n : ℕ) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    (∫⁻ x, (rootedHeatGaussian n q t x : ℝ≥0∞)^q ∂euclideanMeasure n) = 1 := by
  let E := YoungHilbert n
  let K := heatGaussian E t
  have he (x : Rn n) : (rootedHeatGaussian n q t x : ℝ≥0∞)^q =
      ENNReal.ofReal (K (WithLp.toLp 2 x)) := by
    simp only [rootedHeatGaussian,ENNReal.coe_rpow_of_nonneg _ (one_div_pos.mpr hq).le,
      ← ENNReal.rpow_mul,one_div_mul_cancel hq.ne',ENNReal.rpow_one,K]
    rfl
  simp_rw [he]
  have hmk : Measurable (fun y : YoungHilbert n => ENNReal.ofReal (K y)) := by
    dsimp only [K,heatGaussian,E]; fun_prop
  change (∫⁻ x : Rn n, ENNReal.ofReal (K (WithLp.toLp 2 x)) ∂volume) = 1
  rw [(PiLp.volume_preserving_toLp (Fin n)).lintegral_comp hmk]
  have h0 y : 0 ≤ K y := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hi : Integrable K := by
    apply Integrable.const_mul
    simpa using integrable_gaussian_shift (0:E) (by positivity : 0 < (4*t)⁻¹)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0)]
  suffices (∫ x, K x) = 1 by simp [this]
  dsimp only [K,heatGaussian]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < (4*t)⁻¹)]
  have hpi : Real.pi / (4*t)⁻¹ = 4*Real.pi*t := by rw [div_inv_eq_mul]; ring
  rw [hpi,heatNormalization,Real.rpow_def_of_pos (by positivity : 0 < 4*Real.pi*t),← Real.exp_add]
  rw [show -(↑(Module.finrank ℝ E)/2) * Real.log (4*Real.pi*t) +
      Real.log (4*Real.pi*t) * (↑(Module.finrank ℝ E)/2) = 0 by ring,Real.exp_zero]

end LpGowers
