module

public import LpGowers.Euclidean
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! # Affine changes of variables in the family of positive Gaussians -/

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators NNReal
namespace LpGowers

/-- Composing with an invertible affine map and multiplying the amplitude by
a positive constant preserves the Gaussian family in Theorem 1.3. The new
center is T⁻¹(x₀−t) and the quadratic matrix is Tᵀ M T. -/
theorem gaussian_affine_pullback {n : ℕ} {g : Rn n → ℝ≥0} (hg : IsEuclideanGaussian g)
    (T : Rn n ≃L[ℝ] Rn n) (t : Rn n) (a : ℝ≥0) (ha : 0<a) :
    IsEuclideanGaussian (fun x => a*g (T x+t)) := by
  obtain ⟨c,x₀,M,hc,hs,hp,hg⟩ := hg
  let A := LinearMap.toMatrix' T.toLinearEquiv.toLinearMap
  let P := A.transpose*(M*A)
  have hA (v : Rn n) : A *ᵥ v = T v := LinearMap.toMatrix'_mulVec _ v
  have hsym : M.transpose=M := by ext i j; exact hs j i
  have hP : P.transpose=P := by simp [P,Matrix.transpose_mul,hsym,Matrix.mul_assoc]
  have hqd (Q : Matrix (Fin n) (Fin n) ℝ) (v : Rn n) : gaussianQuad Q v = v ⬝ᵥ (Q *ᵥ v) := by
    rw [Matrix.dot_mulVec_eq_sum_sum, gaussianQuad, Finset.sum_comm]
  have hq (v : Rn n) : gaussianQuad P v = gaussianQuad M (T v) := by
    rw [hqd, hqd, show P = A.transpose*(M*A) by rfl, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec, hA]
  refine ⟨(a:ℝ)*c,T.symm (x₀-t),P,mul_pos ha hc,fun i j => ?_,fun v hv => ?_,fun x => ?_⟩
  · exact (congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => Q j i) hP)
  · rw [hq]
    exact hp _ (fun h => hv (T.injective (h.trans T.map_zero.symm)))
  · rw [NNReal.coe_mul, hg, hq, map_sub, T.apply_symm_apply]
    have he : T x+t-x₀ = T x-(x₀-t) := by abel
    rw [he, mul_assoc]

end LpGowers
