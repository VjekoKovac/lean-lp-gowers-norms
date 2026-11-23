module

public import LpGowers.Defs

/-! Theorem 1.1 of Kovač and Rogers, arXiv:2609.08916v2. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace LpGowers

/-- One positive gap for each degree works for every group in the stated
class and every normalization of its Haar measure. -/
def ImprovedLogConvexity : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure],
      (¬ ∃ H : AddSubgroup G, IsCompact (H : Set G) ∧ IsOpen (H : Set G)) →
      ∀ (f : G → ℝ≥0), AEMeasurable f μ →
        ordinaryGowers μ d f ≤ ENNReal.ofReal (1 - ε) *
          ordinaryGowers μ (d - 1) f ^ logTheta d *
          ordinaryGowers μ (d + 1) f ^ (1 - logTheta d)

end LpGowers
