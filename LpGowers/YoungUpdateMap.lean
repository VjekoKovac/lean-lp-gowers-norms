module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The normalized Euler update for the diagonal sharp Young inequality.
The two bilinear maps are the autocorrelation and its adjoint, and the two
pointwise powers are the signed powers of orders s−1 and q′−1. -/
@[expose] public section
namespace LpGowers

/-- Composition defining the nonlinear Young update in real Lebesgue spaces.
For a unit-norm input the normalization is K^(1−q′), where K is the sharp
s-th moment of autocorrelation. -/
def youngUpdateMap {E Y V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (c : ℝ) (A : E →L[ℝ] E →L[ℝ] Y) (B : V →L[ℝ] E →L[ℝ] W)
    (P : Y → V) (Q : W → E) (f : E) : E :=
  c • Q (B (P (A f f)) f)

end LpGowers
