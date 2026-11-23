module

public import LpGowers.DiscreteReflection
import Mathlib.Tactic

/-! The nonnegative generalized Gowers–Cauchy–Schwarz inequality of
Appendix A on discrete groups. At each induction step, Hölder separates
the lower-dimensional cubes, then Cauchy–Schwarz reflects their two faces. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers.Discrete

private theorem tsum_equal_weight_holder {X I : Type*} [Countable X] [Fintype I]
    [Nonempty I] (F : I → X → ℝ≥0∞) {v : ℝ} (hv : 0<v) (hcard : (Fintype.card I : ℝ) = v) :
    (∑' x, ∏ i, F i x) ≤ ∏ i, (∑' x, (F i x)^v)^(1/v) := by
  let : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  have H := ENNReal.lintegral_prod_norm_pow_le (μ:=Measure.count) Finset.univ
    (f:=fun i x => (F i x)^v) (p:=fun _ => 1/v)
    (fun i _ => (measurable_of_countable _).aemeasurable)
    (by simp [hcard,hv.ne']) (fun _ _ => (one_div_pos.mpr hv).le)
  simpa only [lintegral_count, ← ENNReal.rpow_mul, mul_one_div_cancel hv.ne', ENNReal.rpow_one] using H

private theorem gowers_count_zero {G : Type*} [AddCommGroup G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] (k : ℕ) (f : G → ℝ≥0) :
    gowers Measure.count 0 (k+1:ℕ) f = ∑' x, (f x:ℝ≥0∞) := by
  have hp : (k+1:ℕ) ≠ (0:ℝ) := by positivity
  simp only [gowers, lp, autocorrelation, cubeProduct, cubeMeasure_count, lintegral_count, tsum_fintype, Fintype.sum_unique,
    pow_zero, div_one, ENNReal.rpow_one, one_div, ENNReal.rpow_rpow_inv hp]

/-- The generalized Gowers–Cauchy–Schwarz inequality on countable discrete
abelian groups, including all positive integral outer exponents and
extended-valued homogeneous functionals. Each of the `p·2^d` nonnegative
inputs may be chosen independently. -/
theorem mixed_count_holder {G : Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (d k : ℕ) (F : Fin (k+1) → Finset (Fin d) → G → ℝ≥0) :
    (∑' h : Fin d → G, ∏ j, ∑' x : G, ∏ s : Finset (Fin d), (F j s (x + ∑ i ∈ s, h i):ℝ≥0∞)) ≤
      ∏ j, ∏ s, gowers Measure.count d (k+1:ℕ) (F j s) := by
  induction d with
  | zero =>
    apply le_of_eq
    simp only [tsum_fintype, Fintype.sum_unique, Fintype.prod_unique, show (default : Finset (Fin 0)) = ∅ from Subsingleton.elim _ _,
      Finset.sum_empty, add_zero, gowers_count_zero]
  | succ d ih =>
    let V := (2:ℝ)^d * (k+1:ℕ)
    have hV : 0<V := by dsimp [V]; positivity
    let I := Fin (k+1) × Finset (Fin d)
    have hcard : (Fintype.card I : ℝ) = V := by simp [I, V, Fintype.card_finset, mul_comm]
    let H (t : G) (j : Fin (k+1)) (s : Finset (Fin d)) (x : G) :=
      F j (lowerFace s) x * F j (upperFace s) (x+t)
    let N (z : I) (t : G) := gowers Measure.count d (k+1:ℕ) (H t z.1 z.2)
    have split (t : G) (h : Fin d → G) (j : Fin (k+1)) (x : G) :
        (∏ s : Finset (Fin (d+1)), (F j s (x+∑ i ∈ s, Fin.cons t h i):ℝ≥0∞)) =
          ∏ s : Finset (Fin d), (H t j s (x+∑ i ∈ s,h i):ℝ≥0∞) := by
      rw [prod_vertices_succ]
      simp only [H, sum_lowerFace, sum_upperFace, ENNReal.coe_mul, Finset.prod_mul_distrib]
      simp only [add_assoc, add_comm t]
    rw [tsum_fin_cons d]
    simp_rw [split]
    calc
      _ ≤ ∑' t : G, ∏ z : I, N z t := by
        apply tsum_le_tsum
        intro t
        simpa only [N,I,Fintype.prod_prod_type] using ih (H t)
      _ ≤ ∏ z : I, (∑' t, (N z t)^V)^(1/V) := tsum_equal_weight_holder N hV hcard
      _ ≤ ∏ z : I, gowers Measure.count (d+1) (k+1:ℕ) (F z.1 (lowerFace z.2)) *
                    gowers Measure.count (d+1) (k+1:ℕ) (F z.1 (upperFace z.2)) := by
        apply Finset.prod_le_prod
        intro z _
        exact count_face_reflection d k _ _
      _ = _ := by
        rw [Fintype.prod_prod_type]
        apply Finset.prod_congr rfl
        intro j _
        rw [Finset.prod_mul_distrib, prod_vertices_succ]

end LpGowers.Discrete
