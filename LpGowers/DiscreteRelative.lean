module

public import LpGowers.DiscreteVertices

/-! # Relative positions for the mixed cube inequality

Expanding the positive integral power introduces one free base point and
a finite family of further bases. After subtracting the common base, their
relative positions are shared by the two independent translated products.
All sums are nonnegative and permit infinite values.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
namespace LpGowers.Discrete

theorem relative_position_tsum {G : Type*} [AddCommGroup G] [Countable G]
    (k : ℕ) (A B : G → ℝ≥0∞) :
    (∑' t : G, (∑' x : G, A x * B (x+t))^(k+1)) =
      ∑' z : Fin k → G, (∑' y : G, A y * ∏ j, A (y+z j)) *
        (∑' u : G, B u * ∏ j, B (u+z j)) := by
  let P (F : G → ℝ≥0∞) (x : G) (z : Fin k → G) := F x * ∏ i, F (x+z i)
  have hx (t : G) : (∑' x : G, A x * B (x+t))^(k+1) =
      ∑' x : G, ∑' z : Fin k → G, P A x z * P B (x+t) z := by
    let C (x : G) := A x * B (x+t)
    have hpow : (∑' x, C x)^k = ∑' w : Fin k → G, ∏ i, C (w i) := by
      simpa using (tsum_pi_separated k (fun _ => C)).symm
    change (∑' x, C x)^(k+1) = _
    rw [pow_succ', hpow, ← ENNReal.tsum_mul_right]
    apply tsum_congr; intro x
    rw [← ENNReal.tsum_mul_left]
    let e := Equiv.addLeft (fun _ : Fin k => x)
    rw [← e.tsum_eq (fun w => C x * ∏ i, C (w i))]
    apply tsum_congr; intro z
    change (A x * B (x+t)) * (∏ i, A (x+z i) * B (x+z i+t)) = _
    simp only [Finset.prod_mul_distrib, P, add_right_comm x _ t]
    ac_rfl
  change _ = ∑' z : Fin k → G, (∑' y : G, P A y z) * ∑' u : G, P B u z
  simp_rw [hx]
  calc
    _ = ∑' t : G, ∑' z : Fin k → G, ∑' x : G, P A x z * P B (x+t) z := by
      apply tsum_congr; intro t; exact tsum_comm
    _ = ∑' z : Fin k → G, ∑' x : G, ∑' t : G, P A x z * P B (x+t) z := by
      rw [tsum_comm (ι:=G) (ι':=Fin k → G)]
      apply tsum_congr; intro z; exact tsum_comm
    _ = _ := by
      apply tsum_congr; intro z
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr; intro x
      rw [ENNReal.tsum_mul_left]
      exact congrArg (P A x z * ·) ((Equiv.addLeft x).tsum_eq (fun u => P B u z))

end LpGowers.Discrete
