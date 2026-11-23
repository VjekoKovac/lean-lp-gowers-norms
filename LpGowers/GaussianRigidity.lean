module

public import LpGowers.LineMass
public import LpGowers.QuadraticPrimitive
import Mathlib.Tactic

/-! Equality in the heat-flow argument gives an affine logarithmic
differential. Its integral is quadratic, finite mass makes the quadratic
strictly negative definite, and completion of the square identifies the
Gaussian in the coordinates used in Theorem 1.3. -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal BigOperators MatrixOrder
namespace LpGowers

private theorem quad_dot {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x : Rn n) :
    gaussianQuad P x = x ⬝ᵥ (P *ᵥ x) := by
  simp [gaussianQuad,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

/-- A finite positive moment rules out every nonpositive direction in a
symmetric quadratic appearing with a minus sign in the logarithm. -/
theorem positive_quadratic_of_finite_mass {n : ℕ} (f : Rn n → ℝ≥0) (hf : ∀ x, 0<f x)
    (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hquad : ∀ x, Real.log (f x : ℝ) = Real.log (f 0 : ℝ) + x ⬝ᵥ b - gaussianQuad P x)
    {p : ℝ} (hp : 0<p) (hfin : (∫⁻ x, (f x:ℝ≥0∞)^p ∂euclideanMeasure n) ≠ ⊤)
    (v : Rn n) (hv : v≠0) : 0 < gaussianQuad P v := by
  let Q (x : Rn n) := Real.log (f 0 : ℝ) + x ⬝ᵥ b - gaussianQuad P x
  have hfQ (x) : (f x : ℝ) = Real.exp (Q x) :=
    (Real.exp_log (NNReal.coe_pos.mpr (hf x))).symm.trans (congrArg _ (hquad x))
  let F (x : Rn n) := ENNReal.ofReal (Real.exp (Q x*p))
  have hF : Measurable F := by unfold F Q gaussianQuad dotProduct; fun_prop
  have he (x) : F x = (f x:ℝ≥0∞)^p := by
    rw [← ENNReal.ofReal_coe_nnreal, hfQ, ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp.le,
      ← Real.exp_mul]
  have hnf : (∫⁻ x, F x) ≠ ⊤ := by
    change (∫⁻x, F x ∂euclideanMeasure n) ≠ ⊤
    simpa only [he] using hfin
  by_contra! hbad
  apply finite_mass_not_line_subharmonic F hF (fun x => ENNReal.ofReal_pos.mpr (Real.exp_pos _)) hnf v hv
  intro x t
  have hadj : Q (x+t•v) + Q (x+t•(-v)) =
      2*Q x - 2*t^2*gaussianQuad P v := by
    simp only [Q,quad_dot, smul_neg, add_dotProduct, smul_dotProduct, neg_dotProduct,
      Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_add, dotProduct_neg,
      dotProduct_smul, smul_eq_mul]
    ring
  have hnon := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2*t^2 by positivity) hbad
  have Hor : Q x ≤ Q (x+t•v) ∨ Q x ≤ Q (x+t•(-v)) := by
    by_contra! bad
    linarith
  have mono (y : Rn n) (h : Q x ≤ Q y) : F x ≤ F y :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h hp.le))
  rcases Hor with h | h
  · exact (mono _ h).trans (le_add_right le_rfl)
  · exact (mono _ h).trans (le_add_left le_rfl)

/-- A positive exponential affine quadratic with a finite positive-order
moment is a positive-definite Gaussian centered at the unique solution
`P x₀ = b/2`. -/
theorem gaussian_of_affine_log_quadratic {n : ℕ} (f : Rn n → ℝ≥0) (hf : ∀ x, 0<f x)
    (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, P i j=P j i)
    (hquad : ∀ x, Real.log (f x : ℝ) = Real.log (f 0 : ℝ) + x ⬝ᵥ b - gaussianQuad P x)
    {p : ℝ} (hp : 0<p) (hfin : (∫⁻ x, (f x:ℝ≥0∞)^p ∂euclideanMeasure n) ≠ ⊤) :
    IsEuclideanGaussian f := by
  classical
  have hpos := positive_quadratic_of_finite_mass f hf b P hquad hp hfin
  have hP : P.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.ext
      intro i j
      simpa using hs j i
    · intro x hx
      simpa only [star_trivial, ← quad_dot] using hpos x hx
  obtain ⟨o,ho⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hP.isUnit ((1/2:ℝ) • b)
  have hsym : Pᵀ=P := Matrix.ext (fun i j => hs j i)
  have hcross (x) : o ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ o) :=
    (Matrix.dotProduct_transpose_mulVec P o x).symm ▸ by rw [hsym]
  have hcenter (x) : gaussianQuad P (x-o) = gaussianQuad P x - x ⬝ᵥ b + gaussianQuad P o := by
    simp only [quad_dot,Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,hcross x,ho,dotProduct_smul,smul_eq_mul]
    ring
  let c := Real.exp (Real.log (f 0 : ℝ) + gaussianQuad P o)
  refine ⟨c,o,P,Real.exp_pos _,hs,hpos,?_⟩
  intro x
  rw [← Real.exp_log (NNReal.coe_pos.mpr (hf x)),hquad,hcenter]
  dsimp only [c]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The affine-gradient criterion for a smooth density used by the
sharp-Young equality argument. -/
theorem gaussian_of_affine_log_differential {n : ℕ} (f : Rn n → ℝ≥0)
    (hf : ∀ x, 0<f x) (hd : Differentiable ℝ (fun x => Real.log (f x : ℝ)))
    (b : Rn n) (M : Matrix (Fin n) (Fin n) ℝ)
    (H : ∀ x v, fderiv ℝ (fun y => Real.log (f y : ℝ)) x v = v ⬝ᵥ b + v ⬝ᵥ (M *ᵥ x))
    {p : ℝ} (hp : 0<p) (hfin : (∫⁻ x, (f x:ℝ≥0∞)^p ∂euclideanMeasure n) ≠ ⊤) :
    IsEuclideanGaussian f := by
  obtain ⟨P,hs,hquad⟩ := affine_differential_quadratic _ hd b M H
  exact gaussian_of_affine_log_quadratic f hf b P hs hquad hp hfin

/-- An almost-everywhere exponential quadratic with finite positive-order
moment has a Gaussian representative of the form used in Theorem 1.3. -/
theorem gaussian_of_ae_exponential_quadratic {n : ℕ} (f : Rn n → ℝ≥0)
    (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, P i j=P j i)
    (he : ∀ᵐ x ∂euclideanMeasure n, (f x : ℝ)=Real.exp (a + x ⬝ᵥ b - gaussianQuad P x))
    {p : ℝ} (hp : 0<p) (hfin : (∫⁻x, (f x:ℝ≥0∞)^p ∂euclideanMeasure n) ≠ ⊤) :
    ∃ g, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g := by
  let g : Rn n → ℝ≥0 := fun x => (Real.exp (a + x ⬝ᵥ b - gaussianQuad P x)).toNNReal
  have hpos (x) : 0 < g x := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hg (x) : Real.log (g x : ℝ) = a + x ⬝ᵥ b - gaussianQuad P x := by
    simp [g,max_eq_left (Real.exp_nonneg _)]
  have h₀ : Real.log (g 0:ℝ) = a := by simp [hg,gaussianQuad]
  have hfg : f =ᵐ[euclideanMeasure n] g := by
    filter_upwards [he] with x hx
    exact_mod_cast (show (f x:ℝ) = g x by simpa [g,max_eq_left (Real.exp_nonneg _)] using hx)
  have hm := lintegral_congr_ae (hfg.fun_comp (fun z : ℝ≥0 => (z:ℝ≥0∞)^p))
  refine ⟨g,gaussian_of_affine_log_quadratic g hpos b P hs (fun x => ?_) hp (hm ▸ hfin),hfg⟩
  simpa only [h₀] using hg x

end LpGowers
