module

public import LpGowers.Defs

/-! # Theorem 1.4 of Kovač and Rogers

We write the degree as `k+1`, so coordinate deletion leaves exactly `k` increments.
All exponents `q i` are finite, positive real numbers, as in Lemma 2.1 applied with
`bᵢ = qᵢ/2`. The stability threshold is uniform in the group and Haar measure.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

@[expose] public section

noncomputable section
namespace LpGowers

/-- The relation (1.9) and the partition of one from Theorem 1.4. -/
def DegreeParameters (k : ℕ) (p : ℝ) (q θ : Fin (k + 1) → ℝ) : Prop :=
  (∀ i, 0 < q i) ∧ (∑ i, θ i) = 1 ∧
    ∀ i, (1 - 1 / p) / (k : ℝ) = θ i * (1 - ((2 : ℕ) : ℝ) / q i)

/-- The forward inequality includes its endpoint `p=1`. -/
def DegreeForward {k : ℕ} (p : ℝ) (θ : Fin (k + 1) → ℝ) : Prop :=
  0 < p ∧ p ≤ 1 ∧ ∀ i, 0 < θ i

/-- In the reverse inequality exactly the first weight is positive. -/
def DegreeReverse {k : ℕ} (p : ℝ) (θ : Fin (k + 1) → ℝ) : Prop :=
  1 < p ∧ 0 < θ ⟨0, Nat.zero_lt_succ k⟩ ∧ ∀ j : Fin k, θ j.succ < 0

/-- Weighted product of functionals of the lower degree. -/
def lowerProduct {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (k : ℕ) (q θ : Fin (k + 1) → ℝ) (f : G → ℝ≥0) : ℝ≥0∞ :=
  ∏ i, (gowers μ k (q i) f) ^ (θ i)

/-- Both directions of Theorem 1.4(a), with their respective domains. -/
def DegreeInequalities : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p : ℝ) (q θ : Fin (k + 1) → ℝ),
    DegreeParameters k p q θ →
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
      (f : G → ℝ≥0), AEMeasurable f μ →
      (DegreeForward p θ → gowers μ (k + 1) p f ≤ lowerProduct μ k q θ f) ∧
      (DegreeReverse p θ → ¬ (f =ᵐ[μ] fun _ => 0) →
        gowers μ (k + 1) p f < ⊤ → (∀ i, gowers μ k (q i) f < ⊤) →
        lowerProduct μ k q θ f ≤ gowers μ (k + 1) p f)

/-- The integral of the absolute difference of two nonnegative densities.
The sum of the two truncated differences agrees with the ordinary absolute
value wherever the inputs are finite. -/
def l1DensityError {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (u v : X → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, ((u x - v x) + (v x - u x)) ∂ν

/-- Both product approximations in Theorem 1.4(b), using a single family of
probability densities. Their order after deletion is given by `i.succAbove`. -/
def DegreeApproximation {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (k : ℕ) (p : ℝ) (q : Fin (k + 1) → ℝ)
    (f : G → ℝ≥0) (η : ℝ) : Prop :=
  let Rd := autocorrelation μ (k + 1) f
  let Rk := autocorrelation μ k f
  let A := (lp (cubeMeasure μ (k + 1)) p Rd) ^ p
  let B := fun i => (lp (cubeMeasure μ k) (q i) Rk) ^ (q i)
  ∃ r : Fin (k + 1) → G → ℝ≥0,
    (∀ i, Measurable (r i) ∧ (∫⁻ x, (r i x : ℝ≥0∞) ∂μ) = 1) ∧
    l1DensityError (cubeMeasure μ (k + 1)) (fun h => (Rd h) ^ p)
      (fun h => A * ∏ j, (r j (h j) : ℝ≥0∞)) ≤ ENNReal.ofReal η * A ∧
    ∀ i, l1DensityError (cubeMeasure μ k) (fun h => (Rk h) ^ (q i))
      (fun h => B i * ∏ j : Fin k, (r (i.succAbove j) (h j) : ℝ≥0∞)) ≤
      ENNReal.ofReal η * B i

/-- The normalized deficit is measured against the larger side of the
applicable inequality. The same `δ` works for every group, measure and input. -/
def DegreeStability : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p : ℝ) (q θ : Fin (k + 1) → ℝ),
    DegreeParameters k p q θ → p ≠ 1 →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
      (f : G → ℝ≥0), AEMeasurable f μ →
      let U := gowers μ (k + 1) p f
      let P := lowerProduct μ k q θ f
      0 < U → U < ⊤ → (∀ i, 0 < gowers μ k (q i) f ∧ gowers μ k (q i) f < ⊤) →
      ((DegreeForward p θ ∧ ENNReal.ofReal (1 - ε) * P ≤ U) ∨
        (DegreeReverse p θ ∧ ENNReal.ofReal (1 - ε) * U ≤ P)) →
      DegreeApproximation μ k p q f η

/-- The forward and reverse bounds together with quantitative-in-tolerance stability. -/
def DegreeLowering.{u} : Prop := DegreeInequalities.{u} ∧ DegreeStability.{u}

end LpGowers
