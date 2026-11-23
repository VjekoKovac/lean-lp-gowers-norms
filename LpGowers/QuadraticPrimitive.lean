module

public import LpGowers.Euclidean
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! A function with affine differential integrates to an affine quadratic.
The proof restricts to each line through the origin, where the derivative
is affine in the line parameter. -/

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators NNReal ENNReal
namespace LpGowers

/-- On a ray, a differentiable function with derivative `A+tB` equals its
quadratic Taylor polynomial exactly. -/
theorem affine_line_primitive (F : ℝ → ℝ) (A B : ℝ)
    (H : ∀ t, HasDerivAt F (A+t*B) t) (t : ℝ) :
    F t = F 0 + A*t + B*t^2/2 := by
  let P := fun s : ℝ => F 0 + A*s+B*s^2/2
  have hP s : HasDerivAt P (A+s*B) s := by
    dsimp [P]
    convert (((hasDerivAt_const s (F 0)).add ((hasDerivAt_id s).const_mul A)).add
      ((((hasDerivAt_id s).pow 2).const_mul B).div_const 2)) using 1
    · funext u
      simp only [Pi.add_apply, id_eq, Pi.pow_apply]
    · simp only [id_eq]
      ring
  exact isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ
    (fun x _ => (H x).differentiableAt.differentiableWithinAt)
    (fun x _ => (hP x).differentiableAt.differentiableWithinAt)
    (fun x _ => (H x).deriv.trans (hP x).deriv.symm)
    (Set.mem_univ (0:ℝ)) (by simp [P]) (Set.mem_univ t)

/-- In coordinates, an affine differential determines a symmetric quadratic
polynomial. The antisymmetric part of its coefficient matrix drops out. -/
theorem affine_differential_quadratic {n : ℕ} (F : Rn n → ℝ) (hF : Differentiable ℝ F)
    (b : Rn n) (M : Matrix (Fin n) (Fin n) ℝ)
    (H : ∀ x v, fderiv ℝ F x v = v ⬝ᵥ b + v ⬝ᵥ (M *ᵥ x)) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ i j, P i j=P j i) ∧
      ∀ x, F x = F 0 + x ⬝ᵥ b - gaussianQuad P x := by
  let P : Matrix (Fin n) (Fin n) ℝ := fun i j => -(M i j + M j i)/4
  refine ⟨P,fun i j => by dsimp [P]; ring,?_⟩
  intro x
  have hline t : HasDerivAt (fun t : ℝ => F (t • x)) (x ⬝ᵥ b + t*(x ⬝ᵥ (M *ᵥ x))) t := by
    have h := (hF (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    simpa only [Function.comp_def, id_eq, one_smul,H, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] using! h
  have hline1 := affine_line_primitive _ _ _ hline 1
  simp only [one_smul,zero_smul,mul_one,one_pow] at hline1
  rw [hline1]
  have ht : (∑ i, ∑ j, x i * M j i * x j) = ∑ i, ∑ j, x i * M i j * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : gaussianQuad P x = -(x ⬝ᵥ (M *ᵥ x))/2 := by
    have he : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    simp only [gaussianQuad, P, he]
    have f (i j : Fin n) : x i * (-(M i j+M j i)/4)*x j =
        -(x i*M i j*x j)/4 - (x i*M j i*x j)/4 := by ring
    simp only [f, Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_neg_distrib,ht]
    ring
  rw [hp]
  ring

end LpGowers
