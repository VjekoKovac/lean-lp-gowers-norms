module

public import LpGowers.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Euclidean estimates (Theorem 1.3)

The source is V. Kovač and K. M. Rogers, *Estimates for Lᵖ variants of
Gowers norms*, arXiv:2609.08916v2, Theorem 1.3. Lebesgue measure on ℝⁿ
is the product of the one-dimensional Lebesgue measures. All functions
in the theorem take finite nonnegative values. Norms may be infinite in
the universal upper bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LpGowers

noncomputable section

abbrev Rn (n : ℕ) := Fin n → ℝ

def euclideanMeasure (n : ℕ) : Measure (Rn n) :=
  Measure.pi (fun _ : Fin n => (volume : Measure ℝ))

/-- The real sharp constant in Theorem 1.3(a). -/
def sharpEuclideanConstant (d n : ℕ) (p : ℝ) : ℝ :=
  (((2 : ℕ) : ℝ) ^ (2 * d) * p ^ p / ((d : ℝ) + p) ^ ((d : ℝ) + p)) ^
    ((n : ℝ) / (((2 : ℕ) : ℝ) ^ (d + 1) * p))

def gaussianQuad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Rn n) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- Pointwise Gaussians of positive amplitude and arbitrary centre, with
symmetric positive-definite quadratic form. Almost-everywhere agreement
is imposed separately in the classification of equality. -/
def IsEuclideanGaussian {n : ℕ} (g : Rn n → ℝ≥0) : Prop :=
  ∃ (c : ℝ) (x₀ : Rn n) (M : Matrix (Fin n) (Fin n) ℝ),
    0 < c ∧ (∀ i j, M i j = M j i) ∧
    (∀ v : Rn n, v ≠ 0 → 0 < gaussianQuad M v) ∧
    ∀ x, (g x : ℝ) = c * Real.exp (-gaussianQuad M (x - x₀))

/-- One constant works for all nonnegative measurable functions, including
functions whose critical norm is infinite. -/
def EuclideanBound (d n : ℕ) (p : ℝ) (K : ℝ≥0∞) : Prop :=
  ∀ f : Rn n → ℝ≥0, AEMeasurable f (euclideanMeasure n) →
    gowers (euclideanMeasure n) d p f ≤
      K * lp (euclideanMeasure n) (criticalExponent d p) (liftNN f)

/-- The complete target of Theorem 1.3. The last quantifier block is the
epsilon-delta form of a uniform relative error tending to zero. -/
def EuclideanTheorem : Prop :=
  ∀ (d n : ℕ) (p : ℝ), 2 ≤ d → 1 ≤ n → 1 ≤ p →
    let μ := euclideanMeasure n
    let q := criticalExponent d p
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧
    (∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k) ∧
    (∀ f : Rn n → ℝ≥0, AEMeasurable f μ →
      lp μ q (liftNN f) < ⊤ → (¬ f =ᵐ[μ] 0) →
      (gowers μ d p f = K * lp μ q (liftNN f) ↔
        ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[μ] g)) ∧
    (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ f : Rn n → ℝ≥0, AEMeasurable f μ →
        lp μ q (liftNN f) < ⊤ → (¬ f =ᵐ[μ] 0) →
        ENNReal.ofReal (1 - ε) * K * lp μ q (liftNN f) ≤ gowers μ d p f →
        ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧
          lp μ q (liftNN g) = lp μ q (liftNN f) ∧
          lpDist μ q f g ≤ ENNReal.ofReal η * lp μ q (liftNN f))

end

end LpGowers
