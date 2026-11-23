module

public import LpGowers.DiscreteProduct
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Signed increments in the one-dimensional entropy test

Grouping the vertices of a cube with zero and unit signed increments gives the
binomial multiplicities used for the lower estimate in Theorem 1.5(c). -/

@[expose] public section
noncomputable section
open scoped NNReal BigOperators Pointwise
namespace LpGowers.Discrete

def unitShift : Option Bool → ℤ
  | none => 0
  | some false => -1
  | some true => 1

def signedSupport {d : ℕ} (h : Fin d → Option Bool) : ℕ :=
  ∑ i, if (h i).isSome then 1 else 0

def negativeCount {d : ℕ} (h : Fin d → Option Bool) : ℕ :=
  ∑ i, if h i = some false then 1 else 0

private theorem support_le {d : ℕ} (h : Fin d → Option Bool) : signedSupport h ≤ d := by
  unfold signedSupport
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => show (if (h i).isSome then 1 else 0) ≤ 1 by split <;> decide)

def binomialProduct (f : Lattice 1 → ℝ≥0) (k : ℕ) (z : ℤ) : ℝ≥0 :=
  ∏ j ∈ Finset.range (k+1), f (fun _ => z+j) ^ k.choose j

private theorem binomialProduct_succ (f : Lattice 1 → ℝ≥0) (k : ℕ) (z : ℤ) :
    binomialProduct f (k+1) z = binomialProduct f k z * binomialProduct f k (z+1) := by
  simpa [binomialProduct, Nat.cast_add, add_assoc, add_comm (1:ℤ)] using
    Finset.prod_pow_choose_succ (fun j _ => f (fun _ => z+j)) k

/-- At the least admissible base point, the full multilinear weight for a
signed unit cube groups by the number of chosen active directions. -/
theorem finiteCubeProduct_signed (d : ℕ) (f : Lattice 1 → ℝ≥0) (h : Fin d → Option Bool) (z : ℤ) :
    finiteCubeProduct d f (fun i _ => unitShift (h i)) (fun _ => z + negativeCount h) =
      (binomialProduct f (signedSupport h) z)^(2^(d-signedSupport h)) := by
  induction d generalizing z with
  | zero => simp [finiteCubeProduct,binomialProduct,negativeCount,signedSupport]
  | succ d ih =>
    obtain ⟨a,h,rfl⟩ := Fin.exists_cons h
    let v := signedSupport h
    let l := negativeCount h
    have hs : signedSupport (Fin.cons a h) = (if a.isSome then 1 else 0) + v := by
      unfold signedSupport
      rw [Fin.sum_univ_succ]
      rfl
    have hn : negativeCount (Fin.cons a h) = (if a = some false then 1 else 0) + l := by
      unfold negativeCount
      rw [Fin.sum_univ_succ]
      rfl
    have hv : v ≤ d := support_le h
    simp only [finiteCubeProduct,Fin.cons_zero,hn,hs]
    let K := fun (i : Fin d) (_ : Fin 1) => unitShift (h i)
    change finiteCubeProduct d f K (fun _ => z + (((if a = some false then 1 else 0)+l : ℕ):ℤ)) *
      finiteCubeProduct d f K ((fun _ => z + (((if a = some false then 1 else 0)+l : ℕ):ℤ)) +
        (fun _ => unitShift a)) = _
    have ih' (b : ℤ) : finiteCubeProduct d f K (fun _ => b + (l : ℤ)) =
        binomialProduct f v b ^ (2^(d-v)) := ih h b
    cases a with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false, reduceCtorEq, zero_add,
        unitShift]
      have he : d+1-v=(d-v)+1 := by omega
      change finiteCubeProduct d f K (fun _ => z+l) * finiteCubeProduct d f K (fun _ => z+l+0) = _
      simp only [add_zero,ih' z, he, pow_succ (2:ℕ), pow_mul, pow_two]
    | some b =>
      have he : d+1-(1+v)=d-v := by omega
      cases b with
      | false =>
        simp only [Option.isSome_some, ite_true, unitShift, Nat.cast_add, Nat.cast_one, he]
        have hx : (fun _ : Fin 1 => z+(1+(l:ℤ))) = fun _ => (z+1)+l := by funext; ring
        have hx' : (fun _ : Fin 1 => z+(1+(l:ℤ))) + (fun _ => (-1:ℤ)) = fun _ => z+l := by funext; dsimp; ring
        rw [hx',hx,ih' (z+1),ih' z, Nat.add_comm 1 v, binomialProduct_succ,mul_pow,mul_comm]
      | true =>
        simp only [Option.isSome_some, ite_true, Option.some.injEq, Bool.true_eq_false, ite_false,
          zero_add,unitShift,he]
        have hx : (fun _ : Fin 1 => z+(l:ℤ)) + (fun _ => (1:ℤ)) = fun _ => (z+1)+l := by funext; dsimp; ring
        rw [hx,ih' z,ih' (z+1),Nat.add_comm 1 v,binomialProduct_succ,mul_pow]

end LpGowers.Discrete
