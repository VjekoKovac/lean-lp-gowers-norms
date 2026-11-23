module

public import LpGowers.YoungHeatEquality
public import LpGowers.GeometricYoung
public import LpGowers.QuadraticPrimitive
import Mathlib.Tactic

/-! # Quadratic logarithms for smoothed extremizers -/

@[expose] public section
noncomputable section
open MeasureTheory GeometricBrascampLieb Matrix
open scoped Topology BigOperators
namespace LpGowers

/-- A heat convolution with affine logarithmic gradient has quadratic logarithm
in the original real coordinates. -/
theorem heat_exp_quadratic_of_affine_score {n : ℕ} (u : YoungHilbert n → ℝ) (hu : Integrable u)
    (hu0 : ∀ y, 0≤u y) (hum : 0 < ∫ y, u y) {t : ℝ} (ht : 0<t)
    (hScore : let U := convolutionLogHeatFlow hu hu0 hum
      ∃ L : YoungHilbert n →L[ℝ] YoungHilbert n, ∀ x,
        U.gradient t x = L x + U.gradient t 0) :
    ∃ (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, P i j=P j i) ∧ ∀ x : Rn n, heatConvolution u t (WithLp.toLp 2 x) =
        Real.exp (a + x ⬝ᵥ b - gaussianQuad P x) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let U := convolutionLogHeatFlow hu hu0 hum
  let G := U.logValue t ∘ e.symm
  obtain ⟨L,hL⟩ := hScore
  let b : Rn n := e (U.gradient t 0)
  let A : Rn n →ₗ[ℝ] Rn n := e.toLinearMap.comp (L.toLinearMap.comp e.symm.toLinearMap)
  let M := LinearMap.toMatrix' A
  have hdiff (x : Rn n) : HasFDerivAt G
      ((innerSL ℝ (U.gradient t (e.symm x))).comp e.symm.toContinuousLinearMap) x :=
    (U.space_deriv t ht (e.symm x)).comp x e.symm.toContinuousLinearMap.hasFDerivAt
  have heval (x w : Rn n) : fderiv ℝ G x w = w ⬝ᵥ b + w ⬝ᵥ (M *ᵥ x) := by
    rw [(hdiff x).fderiv,LinearMap.toMatrix'_mulVec]
    change inner ℝ (U.gradient t (e.symm x)) (e.symm w) = _
    rw [show U.gradient t (e.symm x) = L (e.symm x)+U.gradient t 0 from hL _,inner_add_left,
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial,star_trivial, add_comm]
    rfl
  obtain ⟨P, hP, hp⟩ := affine_differential_quadratic G (fun x => (hdiff x).differentiableAt) b M heval
  refine ⟨G 0,b,P,hP,fun x => ?_⟩
  rw [← hp x]
  exact (Real.exp_log (heatConvolution_pos hu hu0 hum ht _)).symm

/-- The logarithm of a smoothed frame extremizer is quadratic in the original real
coordinates. The antisymmetric part of the affine score is removed by polarization. -/
theorem heat_exp_quadratic_of_frame_extremal {n : ℕ} {s : ℝ} (hs : 1 < s)
    (u v : YoungHilbert n → ℝ)
    (hu : Integrable u) (hv : Integrable v) (hu0 : ∀ y, 0 ≤ u y) (hv0 : ∀ y, 0 ≤ v y)
    (hum : 0 < ∫ y, u y) (hvm : 0 < ∫ y, v y)
    (hEq : let f : Fin 3 → YoungHilbert n → ℝ := ![u,u,v]
      (∫ y : YoungPair n, ∏ i, (f i (youngFrameMap _ s i y)) ^ youngFrameWeight s i) =
        ∏ i, (∫ y, f i y) ^ youngFrameWeight s i)
    {t : ℝ} (ht : 0 < t) :
    ∃ (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, P i j=P j i) ∧ ∀ x : Rn n, heatConvolution u t (WithLp.toLp 2 x) =
        Real.exp (a + x ⬝ᵥ b - gaussianQuad P x) := by
  exact heat_exp_quadratic_of_affine_score u hu hu0 hum ht
    (affine_heat_score_of_young_frame_extremal hs u v hu hv hu0 hv0 hum hvm hEq ht)

end LpGowers
