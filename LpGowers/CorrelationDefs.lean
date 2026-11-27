module

public import LpGowers.PhaseRemoval
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import LpGowers.Euclidean
import Mathlib.Tactic

/-! # Signed correlation as a bounded bilinear map
Any positive-exponent Young estimate for the extended nonnegative integral lifts
to a genuinely bilinear operator on equivalence classes of real functions.
The representative formula and the constant are preserved. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

abbrev EuclideanLp (n : ℕ) (p : ℝ) : Type := Lp ℝ (ENNReal.ofReal p) (euclideanMeasure n)

/-- The nonnegative inequality whose sharp constant is retained on real Lᵖ. -/
def CorrBound (n : ℕ) (p q r : ℝ) (K : ℝ≥0∞) : Prop :=
  ∀ f g : Rn n → ℝ≥0∞, Measurable f → Measurable g →
    lp (euclideanMeasure n) r (pairCorrelation (euclideanMeasure n) f g) ≤
      K * lp (euclideanMeasure n) p f * lp (euclideanMeasure n) q g

section
variable {n : ℕ}
local notation "ν" => euclideanMeasure n

theorem eLpNorm_eq_lp_real {f : Rn n → ℝ} (hf : AEStronglyMeasurable f ν)
    {a : ℝ} (ha : 0 < a) :
    eLpNorm f (ENNReal.ofReal a) ν = lp ν a (fun x => ‖f x‖ₑ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr ha)
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal ha.le]
  rfl

/-- Reflection as a linear isometry of the real Euclidean Lebesgue space. -/
def reflectLp (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    EuclideanLp n p →ₗᵢ[ℝ] EuclideanLp n p :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (Measure.measurePreserving_neg (volume : Measure (Rn n)))

theorem reflectLp_ae (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (f : EuclideanLp n p) :
    ⇑(reflectLp n p f) =ᵐ[euclideanMeasure n] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure (Rn n)))

end
end LpGowers
