module

public import LpGowers.DiscreteExpansion
public import LpGowers.DiscreteMixed

/-! Appendix A and the product identity (1.12) on the discrete cubes. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
namespace LpGowers.Discrete

/-- The triangle inequality on nonnegative functions for every positive
integer outer exponent on a countable discrete abelian group. -/
theorem gowers_count_triangle {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G] (d k : ℕ) (f g : G → ℝ≥0) :
    gowers Measure.count d (k+1:ℕ) (f+g) ≤
      gowers Measure.count d (k+1:ℕ) f + gowers Measure.count d (k+1:ℕ) g := by
  let U := gowers (Measure.count : Measure G) d ((k+1:ℕ):ℝ)
  have mass : U (f+g) ^ ((2:ℝ)^d*(k+1:ℕ)) = mixedForm d k (fun _ _ => f+g) := by
    rw [show U (f+g) = gowers Measure.count d (k+1:ℕ) (f+g) from rfl, gowers_count_nat_mass]
    simp only [mixedForm,cubeProduct_vertices,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he := mixedForm_add_bound d k U (mixed_count_holder d k) f g
  rw [← mass] at he
  have hp : 0 < (2:ℝ)^d*(k+1:ℕ) := by positivity
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  convert he using 1
  rw [← ENNReal.rpow_natCast]
  simp [U]

/-- Both optimal exponents are attained, and their product is exactly
2^d·p, for every side length n≥2. -/
theorem critical_product (d k n : ℕ) (hn : 2 ≤ n) :
    criticalQ d (k+1) n * criticalT d (k+1) n = (2:ℝ)^d*(k+1:ℕ) :=
  critical_product_of_triangle d k n hn (fun _ f g _ _ => gowers_count_triangle d k f g)

/-- Proposition 8.1 and the reciprocal relation following (1.10). -/
theorem attainment : AttainmentClaim := by
  intro d p n _ hp hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  exact ⟨criticalT_isLeast d k n hn,criticalQ_isGreatest d k n hn,
    (critical_product d k n hn).trans (by push_cast; ring)⟩

end LpGowers.Discrete
