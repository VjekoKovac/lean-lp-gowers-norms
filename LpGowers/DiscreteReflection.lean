module

public import LpGowers.DiscreteRelative
import Mathlib.Tactic

/-! The Cauchy–Schwarz reflection across one cube direction in the
multilinear inequality of Appendix A. Relative base positions make the
counting factors independent even on the infinite lattice. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers.Discrete

theorem tsum_fin_cons {G : Type*} (d : ℕ) (f : (Fin (d+1) → G) → ℝ≥0∞) :
    (∑' h, f h) = ∑' t, ∑' z, f (Fin.cons t z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d+1) => G)).tsum_eq f]
  exact tsum_prod'

private theorem cube_shift_product {G : Type*} [AddCommGroup G] (f g : G → ℝ≥0)
    (d : ℕ) (h : Fin d → G) (t x : G) :
    cubeProduct d (fun x => f x * g (x+t)) h x =
      cubeProduct d f h x * cubeProduct d g h (x+t) := by
  induction d generalizing x with
  | zero => exact ENNReal.coe_mul ..
  | succ d ih =>
    simp only [cubeProduct, ih]
    rw [show x+h 0+t = x+t+h 0 by abel]
    ac_rfl

private theorem tsum_cauchy_schwarz {X : Type*} [Countable X] (a b : X → ℝ≥0∞) :
    (∑' x, a x*b x) ≤ (∑' x, (a x)^2)^(1/2:ℝ) * (∑' x, (b x)^2)^(1/2:ℝ) := by
  let : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure X)
    (Real.holderConjugate_iff.mpr (by norm_num) : Real.HolderConjugate 2 2)
    (measurable_of_countable a).aemeasurable (measurable_of_countable b).aemeasurable
  simpa only [lintegral_count, Pi.mul_apply, ENNReal.rpow_ofNat] using H

private theorem rpow_reflection {A B C : ℝ≥0∞} {v : ℝ} (hv : 0<v)
    (h : A ≤ (B^(2*v))^(1/2:ℝ) * (C^(2*v))^(1/2:ℝ)) :
    A^(1/v) ≤ B*C := by
  have ht : 0≤1/v := (one_div_pos.mpr hv).le
  have H := ENNReal.rpow_le_rpow h ht
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht] at H
  simpa only [← ENNReal.rpow_mul, show (2*v)*(1/2)*(1/v)=1 by field_simp,
    ENNReal.rpow_one] using H

/-- The integral (counting sum) of the lower-dimensional mixed face
functionals is controlled by the two homogeneous upper-dimensional norms. -/
theorem count_face_reflection {G : Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (d k : ℕ) (f g : G → ℝ≥0) :
    (∑' t, gowers Measure.count d (k+1:ℕ) (fun x => f x*g (x+t)) ^ ((2:ℝ)^d*(k+1:ℕ))) ^
        (1/((2:ℝ)^d*(k+1:ℕ))) ≤
      gowers Measure.count (d+1) (k+1:ℕ) f * gowers Measure.count (d+1) (k+1:ℕ) g := by
  let V := (2:ℝ)^d*(k+1:ℕ)
  have hV : 0 < V := by dsimp [V]; positivity
  let Z := (Fin d → G) × (Fin k → G)
  let P (u : G → ℝ≥0) (z : Z) :=
    ∑' y, cubeProduct d u z.1 y * ∏ j, cubeProduct d u z.1 (y + z.2 j)
  have cross (u v : G → ℝ≥0) :
      (∑' t, gowers Measure.count d (k+1:ℕ) (fun x => u x*v (x+t)) ^ V) =
      (∑' z : Z, P u z * P v z) := by
    simp_rw [show V = (2:ℝ)^d*(k+1:ℕ) by rfl, gowers_count_nat_mass, cube_shift_product]
    rw [tsum_comm, tsum_prod']
    exact tsum_congr (fun h => relative_position_tsum k (cubeProduct d u h) (cubeProduct d v h))
  have diag (u : G → ℝ≥0) :
      (∑' z : Z, (P u z)^2) = gowers Measure.count (d+1) (k+1:ℕ) u ^ (2*V) := by
    have he : (2:ℝ)*V = 2^(d+1)*(k+1:ℕ) := by dsimp [V]; rw [pow_succ]; ring
    rw [he,gowers_count_nat_mass,tsum_fin_cons d]
    simp_rw [sq, ← cross u u, show V = (2:ℝ)^d*(k+1:ℕ) by rfl, gowers_count_nat_mass,
      cube_shift_product, cubeProduct, Fin.tail_cons, Fin.cons_zero]
  apply rpow_reflection hV
  rw [cross f g, ← diag, ← diag]
  exact tsum_cauchy_schwarz (P f) (P g)

end LpGowers.Discrete
