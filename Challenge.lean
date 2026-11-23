module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Standalone challenge for the five introductory theorems of arXiv:2609.08916v2.
All local definitions affecting their meaning occur in this file. Deliberate
holes appear only in the advertised Challenge declarations. The Solution is
compiled independently. See docs/REVIEW.md for the scope of the AI audit. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Pointwise Topology Classical

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

namespace LpGowers


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


end LpGowers

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

namespace LpGowers.Discrete

/-- The ambient group is the full integer lattice, without wraparound at the boundary. -/
abbrev Lattice (m : ℕ) := Fin m → ℤ

/-- All lattice points whose coordinates belong to the integer interval [0,n). -/
def box (m n : ℕ) : Finset (Lattice m) :=
  Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) (n : ℤ)

/-- Number of translations of an increment tuple whose entire cube belongs to A.
A subset of the direction indices encodes the binary vertex with that support. -/
def baseCount {G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ}
    (A : Finset G) (h : Fin d → G) : ℕ :=
  (A.filter fun x => ∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ A).card

/-- The shared-increment energy. Each possible increment is a difference of two
elements of A. At fixed h, each of the p ordered base points can be chosen independently. -/
def energy {G : Type*} [AddCommGroup G] [DecidableEq G] (d p : ℕ) (A : Finset G) : ℕ :=
  ∑ h ∈ Fintype.piFinset (fun _ : Fin d => A - A), (baseCount A h) ^ p

/-- Exponents in (1.11), simultaneously for all dimensions including zero. -/
def setExponents (d p n : ℕ) : Set ℝ := {t | 0 < t ∧
  ∀ (m : ℕ) (A : Finset (Lattice m)), A ⊆ box m n →
    ((energy d p A : ℕ) : ℝ) ≤ (A.card : ℝ) ^ t}

/-- Exponents in (1.10) with the counting measure on the full lattice. -/
def functionExponents (d p n : ℕ) : Set ℝ := {q | 0 < q ∧
  ∀ (m : ℕ) (f : Lattice m → ℝ≥0), (∀ x, x ∉ box m n → f x = 0) →
    gowers Measure.count d (p : ℝ) f ≤ lp Measure.count q (liftNN f)}

def criticalT (d p n : ℕ) : ℝ := sInf (setExponents d p n)
def criticalQ (d p n : ℕ) : ℝ := sSup (functionExponents d p n)

/-- Base-two logarithm in §1.3. -/
def logTwo (x : ℝ) : ℝ := Real.logb ((2 : ℕ) : ℝ) x

/-- Shannon entropy of Binomial(k,1/2), measured in bits. -/
def binomialEntropy (k : ℕ) : ℝ :=
  -∑ j ∈ Finset.range (k + 1),
    let a : ℝ := (Nat.choose k j : ℝ) / ((2 : ℕ) : ℝ) ^ k
    a * logTwo a

/-- The coefficient of 1/log₂(n) in the lower bound in (1.13). -/
def correction (d p : ℕ) : ℝ :=
  (((d : ℝ) + p) * logTwo ((d : ℝ) + p) - (p : ℝ) * logTwo p - ((2 : ℕ) : ℝ) * d) / ((2 : ℕ) : ℝ)

/-- Part (a) of Theorem 1.5. -/
def BinaryClaim : Prop := ∀ d p : ℕ, 2 ≤ d → 1 ≤ p →
  criticalT d p 2 = logTwo (((2 : ℕ) : ℝ) ^ p + ((2 : ℕ) : ℝ) * d) ∧
  criticalQ d p 2 = ((2 : ℕ) : ℝ) ^ d * p / logTwo (((2 : ℕ) : ℝ) ^ p + ((2 : ℕ) : ℝ) * d)

/-- Part (b). The positive c is absolute. The error and the threshold in n may
depend on the fixed d,p. -/
def LargeSideClaim : Prop := ∃ c : ℝ, 0 < c ∧ ∀ d p : ℕ, 2 ≤ d → 1 ≤ p →
  ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
    ((d : ℝ) + p - (1 + e n) * correction d p / logTwo n ≤ criticalT d p n ∧
      criticalT d p n ≤ (d : ℝ) + p - c / logTwo n)

/-- Main term in part (c), with an additive error tending to zero. -/
def largeDegreeMainTerm (n d : ℕ) : ℝ :=
  (((n - 1 : ℕ) : ℝ) * logTwo (((2 : ℕ) : ℝ) * (d : ℝ)) - logTwo (Nat.factorial (n - 1))) /
    binomialEntropy (n - 1)

/-- Part (c). The limit is taken over d with both n and p fixed. -/
def LargeDegreeClaim : Prop := ∀ n p : ℕ, 2 ≤ n → 1 ≤ p →
  Tendsto (fun d : ℕ => criticalT d p n - largeDegreeMainTerm n d) atTop (𝓝 0)

def DiscreteClaim : Prop := BinaryClaim ∧ LargeSideClaim ∧ LargeDegreeClaim

/-- Ancillary conclusion of Proposition 8.1, explicitly distinguished from Theorem 1.5. -/
def AttainmentClaim : Prop := ∀ d p n : ℕ, 2 ≤ d → 1 ≤ p → 2 ≤ n →
  IsLeast (setExponents d p n) (criticalT d p n) ∧
    IsGreatest (functionExponents d p n) (criticalQ d p n) ∧
    criticalQ d p n * criticalT d p n = (p : ℝ) * ((2 : ℕ) : ℝ) ^ d

end LpGowers.Discrete

namespace LpGowers

/-- Theorem 1.1 of Kovač–Rogers. -/
theorem theorem_1_1 : ImprovedLogConvexity := by sorry

/-- Theorem 1.2 of Kovač–Rogers. -/
theorem theorem_1_2 : LebesgueEstimate := by sorry

/-- Theorem 1.3 of Kovač–Rogers. -/
theorem theorem_1_3 : EuclideanTheorem := by sorry

/-- Theorem 1.4 of Kovač–Rogers. -/
theorem theorem_1_4 : DegreeLowering := by sorry

/-- Theorem 1.5 of Kovač–Rogers. -/
theorem theorem_1_5 : Discrete.DiscreteClaim := by sorry

/-- The complete sharp inequality, optimality and equality classification of Theorem 1.3(a). -/
theorem theorem_1_3a (d n : ℕ) (p : ℝ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    let μ := euclideanMeasure n
    let q := criticalExponent d p
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧
    (∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k) ∧
    (∀ f : Rn n → ℝ≥0, AEMeasurable f μ →
      lp μ q (liftNN f) < ⊤ → (¬ f =ᵐ[μ] 0) →
      (gowers μ d p f = K * lp μ q (liftNN f) ↔
        ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[μ] g)) := by
  sorry

end LpGowers

namespace LpGowers.Checked

theorem subgroupIndicator {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) =
      μ (H : Set G) ^ (((d : ℝ) + p) / ((2 : ℝ) ^ d * p)) := by
  sorry

theorem marginal {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) (k : ℕ) (i : Fin (k + 1)) (h : Fin k → G) :
    (∫⁻ t, autocorrelation μ (k + 1) f (i.insertNth (α := fun _ => G) t h) ∂μ) =
       (autocorrelation μ k f h) ^ (2 : ℕ) := by
  sorry

theorem degreeOneExponent {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) (q θ : Fin (k + 1) → ℝ)
    (h : DegreeParameters k 1 q θ) (hθ : DegreeForward 1 θ) :
    gowers μ (k + 1) 1 f = lowerProduct μ k q θ f := by
  sorry

theorem exactMoments {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hA : (∫⁻ x, F x ^ a ∂μ) = 1) (hB : (∫⁻ x, F x ^ b ∂μ) = 1)
    (hC : (∫⁻ x, F x ^ c ∂μ) = 1) :
    ∀ᵐ x ∂μ, F x = 0 ∨ F x = 1 := by
  sorry

theorem scalarGaussianCorrelation (a : ℝ) (ha : 0 < a) (d : ℕ) (h : Fin d → ℝ) :
    autocorrelation volume d (fun x => (Real.exp (-a * x ^ 2)).toNNReal) h =
      ENNReal.ofReal (Real.exp (-(a * 2 ^ d) * ((∑ i, h i ^ 2) / 4))) *
      ENNReal.ofReal (Real.sqrt (Real.pi / (a * 2 ^ d))) := by
  sorry

theorem binaryEnergy (d k : ℕ) :
    Discrete.energy d (k + 1) ({0, 1} : Finset (Discrete.Lattice 1)) =
      2 ^ (k + 1) + 2 * d := by
  sorry

theorem binaryLower (d k : ℕ) :
    Discrete.logTwo ((2 : ℝ) ^ (k + 1) + 2 * d) ≤ Discrete.criticalT d (k + 1) 2 := by
  sorry

theorem finiteInterpolation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {p a b θ : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (h : 1 / p = θ / a + (1 - θ) / b) :
    lp μ p F ≤ lp μ a F ^ θ * lp μ b F ^ (1 - θ) := by
  sorry

/-- The sharp upper bound from Theorem 1.3(a) and the least admissible constant. -/
theorem euclideanSharpEstimate (d n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧ ∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k := by
  sorry

theorem gaussianEquality (d n : ℕ) (p : ℝ) (hp : 0 < p) :
    let g := fun x : Rn n => ∏ i, (Real.exp (-Real.pi * x i ^ 2)).toNNReal
    gowers (euclideanMeasure n) d p g = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN g) := by
  sorry

theorem euclideanNecessaryConstant (d n : ℕ) (p : ℝ) (hp : 0 < p)
    (K : ℝ≥0∞) (hK : EuclideanBound d n p K) :
    ENNReal.ofReal (sharpEuclideanConstant d n p) ≤ K := by
  sorry

theorem largeSideLimit (d k : ℕ) :
    Filter.Tendsto (Discrete.criticalT d (k + 1)) Filter.atTop
      (𝓝 ((d + (k + 1) : ℕ) : ℝ)) := by
  sorry

theorem lebesgueInequality.{u} : LebesgueBound.{u} := by
  sorry

theorem degreeInequalities.{u} : DegreeInequalities.{u} := by
  sorry

theorem ordinaryLogConvex {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    ordinaryGowers μ d f ≤ ordinaryGowers μ (d - 1) f ^ logTheta d *
      ordinaryGowers μ (d + 1) f ^ (1 - logTheta d) := by
  sorry

theorem allGaussianEquality {n : ℕ} (d : ℕ) (p : ℝ) (hp : 0 < p) (f : Rn n → ℝ≥0)
    (h : ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g) :
    gowers (euclideanMeasure n) d p f = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN f) := by
  sorry

theorem binarySetExponent : Discrete.criticalT 2 2 2 = 3 := by
  sorry

theorem binaryEnergyAllDimensions (m d k : ℕ) :
    Discrete.energy d (k + 1) (Discrete.box m 2) = (2 ^ (k + 1) + 2 * d) ^ m := by
  sorry

theorem setAttainment (d k n : ℕ) (hn : 2 ≤ n) :
    IsLeast (Discrete.setExponents d (k + 1) n) (Discrete.criticalT d (k + 1) n) := by
  sorry

theorem functionAttainment (d k n : ℕ) (hn : 2 ≤ n) :
    IsGreatest (Discrete.functionExponents d (k + 1) n) (Discrete.criticalQ d (k + 1) n) := by
  sorry

theorem productUpper (d k n : ℕ) (hn : 2 ≤ n) :
    Discrete.criticalQ d (k + 1) n * Discrete.criticalT d (k + 1) n ≤
      (2 : ℝ) ^ d * (k + 1 : ℕ) := by
  sorry

theorem binaryLargeDegree (k : ℕ) :
    Filter.Tendsto (fun d : ℕ => Discrete.criticalT d (k + 1) 2 /
      Discrete.logTwo (2 * (d : ℝ))) Filter.atTop (𝓝 1) := by
  sorry

theorem nearThreeMoments {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ), 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ),
    Measurable F → (∀ x, 0 ≤ F x) →
    (∀ s ∈ ({a,b,c} : Set ℝ), Integrable (fun x => F x ^ s) μ ∧
      |(∫ x, F x ^ s ∂μ) - 1| ≤ ε) →
    let E := {x | 1/2 < F x}
    MeasurableSet E ∧ μ E < ⊤ ∧ |μ.real E - 1| ≤ η ∧
      ∀ t ∈ Set.Icc a c, Integrable (fun x => |F x - E.indicator 1 x| ^ t) μ ∧
        (∫ x, |F x - E.indicator 1 x| ^ t ∂μ) ≤ η := by
  sorry

theorem binaryBothExponents :
    Discrete.criticalT 2 2 2 = 3 ∧ Discrete.criticalQ 2 2 2 = 8 / 3 := by
  sorry

/-- The full diagonal leakage inequality, Lemma 6.3 of the paper. -/
theorem diagonalLeakage {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A : Set G} (hA : NullMeasurableSet A μ) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0 + h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, ∫⁻ x, liftNN f x * liftNN f (x + s) ∂μ ∂μ) ^ (1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  sorry

/-- Both optimal exponents in Theorem 1.5(a), for every degree and outer exponent in the source. -/
theorem binarySharp : Discrete.BinaryClaim := by
  sorry

/-- Both lattice exponents are attained, with the equality in equation (1.12). -/
theorem criticalExponents : Discrete.AttainmentClaim := by
  sorry

/-- Both logarithmic estimates in Theorem 1.5(b), with one absolute upper-deficit constant. -/
theorem largeSideSharp : Discrete.LargeSideClaim := by
  sorry

/-- The lower inequality in the additive entropy asymptotic of Theorem 1.5(c). -/
theorem largeDegreeLower (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, Discrete.largeDegreeMainTerm n d - η ≤ Discrete.criticalT d p n := by
  sorry

end LpGowers.Checked
