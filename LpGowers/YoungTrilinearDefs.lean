module

public import LpGowers.EuclideanYoung

/-! The trilinear form of the sharp Euclidean Young estimate in §4. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LpGowers

/-- Dual pairing for the sharp Young estimate with two equal input
exponents. The normalization is the one used in `SharpDiagonalYoung`. -/
def SharpYoungTrilinear (n : ℕ) : Prop :=
  ∀ s : ℝ, 1 < s → ∀ F G H : Rn n → ℝ≥0∞,
    Measurable F → Measurable G → Measurable H →
    let μ := euclideanMeasure n
    (∫⁻ t, (∫⁻ x, F x*G (x+t) ∂μ)*H t ∂μ) ≤
      (ENNReal.ofReal (diagonalYoungFactor s)^n)^(1/s) *
        lp μ (2*s/(s+1)) F * lp μ (2*s/(s+1)) G * lp μ (s/(s-1)) H

end LpGowers
