module

public import LpGowers.Defs

/-! # Theorem 1.2 of Kovač–Rogers

The near-extremiser conclusion is written in uniform tolerance form. Once
`d,p` and the desired relative error `η` are fixed, one threshold `δ` works
across all admissible groups, Haar measures, and inputs. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LpGowers

/-- The lower endpoint in Theorem 1.2(a), excluded in its stability clause. -/
def lowerEndpoint (d : ℕ) : ℝ := d / (((2 : ℕ) : ℝ) ^ d - 1)

/-- The coset `x₀ + H` carries a constant value determined by its measure
and by the requested norm `N`. In the stability conclusion `H` is compact
and open, `N` is finite, and the exponent `q` is positive. -/
def cosetProfile {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    (μ : Measure G) (q : ℝ) (N : ℝ≥0∞) (H : AddSubgroup G) (x₀ : G) :
    G → ℝ≥0 := by
  classical
  exact fun x => if x - x₀ ∈ H then (N / (μ (H : Set G)) ^ (1 / q)).toNNReal else 0

/-- Theorem 1.2(a). -/
def LebesgueBound : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ p : ℝ, lowerEndpoint d ≤ p →
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0), AEMeasurable f μ →
      gowers μ d p f ≤ lp μ (criticalExponent d p) (liftNN f)

/-- Theorem 1.2(b). The input is nonzero modulo null sets, has finite critical
norm and approaches the optimal constant one. -/
def LebesgueStability : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ p : ℝ, lowerEndpoint d < p →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0), AEMeasurable f μ →
      ¬ (f =ᵐ[μ] fun _ => 0) →
      let q := criticalExponent d p
      let N := lp μ q (liftNN f)
      N < ⊤ → ENNReal.ofReal (1 - ε) * N ≤ gowers μ d p f →
      ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
        lpDist μ q f (cosetProfile μ q N H x₀) ≤ ENNReal.ofReal η * N

/-- Both clauses of the second introductory theorem. -/
def LebesgueEstimate.{u} : Prop := LebesgueBound.{u} ∧ LebesgueStability.{u}

end LpGowers
