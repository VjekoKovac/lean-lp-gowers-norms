module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Nonnegative cube integrals

The five statements in the introduction of Kovač–Rogers concern nonnegative
functions. Their conjugations therefore disappear from the cube product.
The cube product splits its vertices by the first bit. Its two factors are
the lower-dimensional cubes based at `x` and at `x+h₁`.
All integrals have extended nonnegative values, including for nonintegrable
inputs. The exponent supplied to `lp` and `gowers` is finite and positive
in every main statement.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace LpGowers

/-- Product measure on the ordered increments `h₁,…,h_d`. -/
def cubeMeasure {G : Type*} [MeasurableSpace G] (μ : Measure G) (d : ℕ) :
    Measure (Fin d → G) :=
  Measure.pi (fun _ : Fin d => μ)

/-- Regard a finite nonnegative function as an extended nonnegative function. -/
def liftNN {G : Type*} (f : G → ℝ≥0) (x : G) : ℝ≥0∞ := f x

/-- The product of the values at all `2^d` vertices based at `x` with increments `h`. -/
def cubeProduct {G : Type*} [AddCommMonoid G] :
    (d : ℕ) → (G → ℝ≥0) → (Fin d → G) → G → ℝ≥0∞
  | 0, f, _, x => f x
  | d + 1, f, h, x =>
      cubeProduct d f (Fin.tail h) x * cubeProduct d f (Fin.tail h) (x + h 0)

/-- The multiple autocorrelation `R_d f` of a nonnegative function. -/
def autocorrelation {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (d : ℕ) (f : G → ℝ≥0) (h : Fin d → G) : ℝ≥0∞ :=
  ∫⁻ x, cubeProduct d f h x ∂μ

/-- Extended Lebesgue functional for positive finite `p`, including `p < 1`. -/
def lp {G : Type*} [MeasurableSpace G] (μ : Measure G) (p : ℝ)
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p)

/-- The `L^p` quantity of the difference of two nonnegative finite functions. -/
def lpDist {G : Type*} [MeasurableSpace G] (μ : Measure G) (p : ℝ)
    (f g : G → ℝ≥0) : ℝ≥0∞ :=
  lp μ p (fun x => edist (f x) (g x))

/-- The nonnegative Gowers-type functional `[f]_{U^{d,p}(G)}`. -/
def gowers {G : Type*} [MeasurableSpace G] [AddCommMonoid G] (μ : Measure G)
    (d : ℕ) (p : ℝ) (f : G → ℝ≥0) : ℝ≥0∞ :=
  (lp (cubeMeasure μ d) p (autocorrelation μ d f)) ^ (1 / (2 : ℝ) ^ d)

/-- The ordinary Gowers functional for nonnegative `f`. -/
def ordinaryGowers {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (d : ℕ) (f : G → ℝ≥0) : ℝ≥0∞ :=
  gowers μ d 1 f

/-- The input exponent in the Lebesgue estimates. -/
def criticalExponent (d : ℕ) (p : ℝ) : ℝ := 2 ^ d * p / (d + p)

/-- The interpolation weight in the log-convexity theorem. -/
def logTheta (d : ℕ) : ℝ := d / (3 * (d : ℝ) - 2)

end LpGowers
