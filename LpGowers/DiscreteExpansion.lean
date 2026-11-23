module

public import LpGowers.DiscreteDyadic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The binary expansion used in the triangle inequality of Appendix A:
expand separately at all p·2^d places, apply mixed Gowers–Cauchy–Schwarz
to each term, and collect the scalar binomial expansion. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
namespace LpGowers.Discrete

/-- Sum over the common increments and the independent base point of each cube. -/
def mixedForm {G : Type*} [AddCommGroup G] (d k : ℕ)
    (F : Fin (k+1) → Finset (Fin d) → G → ℝ≥0) : ℝ≥0∞ :=
  ∑' h : Fin d → G, ∏ j, ∑' x : G, ∏ s : Finset (Fin d), (F j s (x + ∑ i ∈ s, h i) : ℝ≥0∞)

private theorem sum_choices {α β : Type*} [Fintype β] (f : α → β → ℝ≥0∞) :
    (∑' x, ∑ y, f x y) = ∑ y, ∑' x, f x y := by
  exact Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)

/-- Expanding the diagonal energy of a sum into all mixed energies. -/
theorem mixedForm_binary_expansion {G : Type*} [AddCommGroup G] (d k : ℕ)
    (f : Bool → G → ℝ≥0) :
    mixedForm d k (fun _ _ x => ∑ b, f b x) =
      ∑ χ : Fin (k+1) → Finset (Fin d) → Bool, mixedForm d k (fun j s => f (χ j s)) := by
  let vertex (h : Fin d → G) (x : G) (s : Finset (Fin d)) (b : Bool) : ℝ≥0∞ :=
    f b (x + ∑ i ∈ s, h i)
  let block (h : Fin d → G) (c : Finset (Fin d) → Bool) := ∑' x, ∏ s, vertex h x s (c s)
  have eqBlock (h : Fin d → G) :
      (∑' x : G, ∏ s : Finset (Fin d), ∑ b, vertex h x s b) = ∑ c, block h c := by
    simp_rw [Fintype.prod_sum]
    exact sum_choices _
  unfold mixedForm
  have liftSum (x : G) : ((∑ b, f b x : ℝ≥0) : ℝ≥0∞) = ∑ b, (f b x : ℝ≥0∞) := by
    simp
  simp only [liftSum]
  change (∑' h, ∏ _j : Fin (k+1), ∑' x : G, ∏ s : Finset (Fin d), ∑ b, vertex h x s b) = _
  simp_rw [eqBlock, Fintype.prod_sum]
  exact sum_choices _

/-- If the mixed estimate holds for the given functionals, the diagonal
mixed moment of f+g is bounded by the N-th power of the sum of the two
bounds, with the exact integer N = 2^d (k+1). -/
theorem mixedForm_add_bound {G : Type*} [AddCommGroup G] (d k : ℕ) (U : (G → ℝ≥0) → ℝ≥0∞)
    (hMixed : ∀ F : Fin (k+1) → Finset (Fin d) → G → ℝ≥0,
      mixedForm d k F ≤ ∏ j, ∏ s, U (F j s)) (f g : G → ℝ≥0) :
    mixedForm d k (fun _ _ => f+g) ≤ (U f + U g)^(2^d * (k+1)) := by
  let V : Bool → G → ℝ≥0 := fun b => if b then f else g
  have hV : (fun x => ∑ b, V b x) = f+g := by funext x; simp [V]
  rw [← hV, mixedForm_binary_expansion]
  apply (Finset.sum_le_sum fun χ _ => hMixed (fun j s => V (χ j s))).trans_eq
  calc
    _ = ∏ _j : Fin (k+1), ∑ c : Finset (Fin d) → Bool, ∏ s, U (V (c s)) :=
      (Fintype.prod_sum (fun (_j : Fin (k+1)) (c : Finset (Fin d) → Bool) => ∏ s, U (V (c s)))).symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (_s : Finset (Fin d)) (b : Bool) => U (V b))]
      simp [V, ← pow_mul]

end LpGowers.Discrete
