module

public import LpGowers.Defs

/-! Combined error in the box approximation in §6. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

/-- The combined integrand for L¹ error and squared L² error. -/
def boxErrorAt (u v : ℝ≥0∞) : ℝ≥0∞ :=
  let b := (u-v)+(v-u)
  b + b^2

/-- The box error is integrated against the actual product Haar measure. -/
def boxError {G : Type*} [AddCommMonoid G] [MeasurableSpace G] (μ : Measure G)
    (d : ℕ) (f : G → ℝ≥0) (A : Fin d → Set G) :=
  ∫⁻ h, boxErrorAt (autocorrelation μ d f h) ((Set.univ.pi A).indicator (fun _ => (1 : ℝ≥0∞)) h)
    ∂cubeMeasure μ d

end LpGowers
