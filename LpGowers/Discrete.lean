module

public import LpGowers.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.Pi

/-!
# The two critical exponents on integer cubes

Source: Kovač and Rogers, arXiv:2609.08916v2, §1.3, (1.10)–(1.13),
Theorem 1.5, and the attainment assertion in Proposition 8.1.
-/
@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Pointwise Topology

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
