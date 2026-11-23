module

public import LpGowers.GeometricYoung
public import LpGowers.YoungDuality
public import LpGowers.EuclideanInverse
public import GeometricBrascampLieb.FrameDatum
public import GeometricBrascampLieb.MeasurableInequality

/-! # The sharp Euclidean estimate and optimality

Yi Han's geometric Brascamp–Lieb proof supplies the three-map inequality.
The coordinate changes and the nonlinear Young duality are proved in this
project. Iterating that inequality gives the upper bound of Theorem 1.3(a),
with equality for the positive-definite Gaussian family and optimal constant.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

/-- Yi Han's geometric Brascamp–Lieb theorem applied to this explicit
higher-rank coisometric datum. -/
theorem young_frame_bound (n : ℕ) (s : ℝ) (hs : 1<s) : YoungFrameBound n s := by
  let V := YoungHilbert n
  let D : GeometricBrascampLieb.Datum (Fin 3) (YoungPair n) (fun _ => V) :=
    GeometricBrascampLieb.Datum.ofNormSq (youngFrameMap V s) (youngFrameWeight s)
      (youngFrameWeight_nonneg hs.le) (youngFrameMap_coisometry V (zero_lt_one.trans hs))
      (youngFrameMap_resolution V (zero_lt_one.trans hs))
  intro U hU
  exact D.lintegral_prod_le U hU

/-- Sharp diagonal Young in every finite Euclidean dimension, with all
measurable nonnegative input functions. -/
theorem sharp_diagonal_young (n : ℕ) : SharpDiagonalYoung n :=
  sharpDiagonalYoung_of_trilinear n (sharpYoungTrilinear_of_frame n (young_frame_bound n))

/-- The sharp universal estimate and the minimality of its constant in Theorem 1.3(a). -/
theorem euclidean_sharp_estimate (d n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧ ∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k :=
  ⟨euclideanBound_of_sharpDiagonalYoung (sharp_diagonal_young n) d p hp,
    euclideanConstant_le_of_bound d n p (zero_lt_one.trans_le hp)⟩

/-- The remaining inverse input is the exact and near Gaussian classification
for the ordinary diagonal Young inequality. -/
theorem euclideanTheorem_of_inverse (hInv : ∀ n : ℕ, 1 ≤ n → SharpYoungInverse n) :
    EuclideanTheorem :=
  euclideanTheorem_of_sharpYoung_and_inverse (fun n _ => sharp_diagonal_young n) hInv

end LpGowers
