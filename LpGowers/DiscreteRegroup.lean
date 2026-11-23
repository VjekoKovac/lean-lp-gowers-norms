module

public import LpGowers.DiscreteEntropyTest
public import LpGowers.DiscreteVertices
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Tactic

/-! # Grouping one-dimensional energies by the number of active increments

The coefficient for `l` active directions is precisely `d.choose l`.
Each of the remaining positions duplicates all vertices and hence gives one
factor of two in the exponent. This is the grouping preceding (8.3). -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Pointwise
namespace LpGowers.Discrete

private def stepInput {G : Type*} [AddCommGroup G] (u : G) (f : G → ℝ≥0) (x : G) : ℝ≥0 := f x * f (x+u)

private theorem cube_step {G : Type*} [AddCommGroup G] (l : ℕ) (f : G → ℝ≥0) (u : G)
    (h : Fin l → G) (x : G) : finiteCubeProduct l (stepInput u f) h x =
    finiteCubeProduct l f h x * finiteCubeProduct l f h (x+u) := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    simp only [finiteCubeProduct,ih,add_right_comm x _ u]
    ac_rfl

private theorem cube_sq {G : Type*} [AddCommGroup G] (l : ℕ) (f : G → ℝ≥0) (h : Fin l → G) (x : G) :
    finiteCubeProduct l (stepInput 0 f) h x = finiteCubeProduct l f h x ^ 2 := by
  rw [cube_step,add_zero,pow_two]

private theorem sum_steps_succ {G : Type*} [DecidableEq G] (D : Finset G) (l : ℕ)
    (v : (Fin (l+1) → G) → ℝ≥0) :
    (∑ h ∈ Fintype.piFinset (fun _ : Fin (l+1) => D), v h) =
      ∑ a ∈ D, ∑ h ∈ Fintype.piFinset (fun _ : Fin l => D), v (Fin.cons a h) := by
  have E := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (l+1) => D) (fun _ => True)
  simp only [Finset.filter_true] at E
  rw [E,Finset.sum_map,Finset.sum_product]
  rfl

/-- The contribution of a compressed cube with `l` active directions and
`r` further zero directions. -/
def activeSum {G : Type*} [AddCommGroup G] (A D : Finset G) (p l r : ℕ) (f : G → ℝ≥0) : ℝ≥0 :=
  ∑ h ∈ Fintype.piFinset (fun _ : Fin l => D), (∑ x ∈ A, finiteCubeProduct l f h x ^ (2^r))^p

private theorem activeStep {G : Type*} [AddCommGroup G] [DecidableEq G] (A D : Finset G) (p l r : ℕ)
    (f : G → ℝ≥0) : activeSum A D p (l+1) r f = ∑ u ∈ D, activeSum A D p l r (stepInput u f) := by
  unfold activeSum
  rw [sum_steps_succ]
  simp only [finiteCubeProduct,Fin.tail_cons,Fin.cons_zero,cube_step]

private theorem activeZero {G : Type*} [AddCommGroup G] (A D : Finset G) (p l r : ℕ)
    (f : G → ℝ≥0) : activeSum A D p l r (stepInput 0 f) = activeSum A D p l (r+1) f := by
  unfold activeSum
  simp only [cube_sq,← pow_mul,pow_succ' (2:ℕ) r]

/-- Exact binomial regrouping of the finite energy by nonzero increments,
valid on any abelian group and any finite set containing a point. -/
theorem weightedEnergy_regroup {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G)
    (hA : A.Nonempty) (d p : ℕ) (f : G → ℝ≥0) :
    weightedEnergy d p A f = ∑ l ∈ Finset.range (d+1),
      (d.choose l : ℝ≥0) * activeSum A ((A-A).erase 0) p l (d-l) f := by
  classical
  let D := (A-A).erase 0
  have h0 : 0 ∈ A-A := by obtain ⟨a,ha⟩ := hA; exact Finset.mem_sub.mpr ⟨a,ha,a,ha,sub_self _⟩
  induction d generalizing f with
  | zero => simp [weightedEnergy,activeSum]
  | succ d ih =>
    have hrec : weightedEnergy (d+1) p A f = ∑ u ∈ A-A, weightedEnergy d p A (stepInput u f) := by
      unfold weightedEnergy
      rw [sum_steps_succ]
      simp only [finiteCubeProduct,Fin.tail_cons,Fin.cons_zero,cube_step]
    rw [hrec,← Finset.add_sum_erase _ _ h0]
    simp only [ih]
    rw [Finset.sum_choose_succ_mul (fun l r => activeSum A D p l r f)]
    congr 1
    · apply Finset.sum_congr rfl
      intro l hl
      have h : d+1-l=d-l+1 := by have := Finset.mem_range.mp hl; omega
      simp only [activeZero,h,D]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [activeStep,Finset.mul_sum]

end LpGowers.Discrete
