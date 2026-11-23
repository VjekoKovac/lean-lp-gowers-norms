module

public import LpGowers.DiscreteFunctional
public import LpGowers.ProductIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Finite cube vertices and unrestricted counting sums in Appendix A.
The two maps below label the opposite faces perpendicular to the first
increment. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers.Discrete

def lowerFace {d : ℕ} (s : Finset (Fin d)) : Finset (Fin (d+1)) :=
  s.map (Fin.succEmb d)
def upperFace {d : ℕ} (s : Finset (Fin d)) : Finset (Fin (d+1)) :=
  insert 0 (lowerFace s)

private def splitVertex (d : ℕ) : Bool × Finset (Fin d) ≃ Finset (Fin (d+1)) where
  toFun z := if z.1 then upperFace z.2 else lowerFace z.2
  invFun s := (decide (0 ∈ s), Finset.univ.filter (fun i => i.succ ∈ s))
  left_inv := by
    rintro ⟨b,s⟩
    cases b <;> simp [upperFace, lowerFace]
  right_inv s := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> by_cases h : (0 : Fin (d+1)) ∈ s <;>
      simp [upperFace, lowerFace, h]

theorem prod_vertices_succ {M : Type*} [CommMonoid M] {d : ℕ}
    (u : Finset (Fin (d+1)) → M) :
    ∏ s, u s = (∏ s, u (lowerFace s)) * ∏ s, u (upperFace s) := by
  rw [← (splitVertex d).prod_comp u, Fintype.prod_prod_type]
  simp [splitVertex, mul_comm]

@[simp] theorem sum_lowerFace {G : Type*} [AddCommMonoid G] {d : ℕ}
    (a : G) (h : Fin d → G) (s : Finset (Fin d)) :
    ∑ i ∈ lowerFace s, Fin.cons a h i = ∑ i ∈ s, h i := by simp [lowerFace]
@[simp] theorem sum_upperFace {G : Type*} [AddCommMonoid G] {d : ℕ}
    (a : G) (h : Fin d → G) (s : Finset (Fin d)) :
    ∑ i ∈ upperFace s, Fin.cons a h i = a + ∑ i ∈ s, h i := by
  simp [upperFace, lowerFace]

/-- The recursive product in the LCA definition is the product of the
input over the subset-indexed vertices of the additive cube. -/
theorem cubeProduct_vertices {G : Type*} [AddCommMonoid G] (d : ℕ) (f : G → ℝ≥0)
    (h : Fin d → G) (x : G) :
    cubeProduct d f h x = ∏ s : Finset (Fin d), (f (x+∑ i ∈ s, h i):ℝ≥0∞) := by
  induction d generalizing x with
  | zero =>
    rw [Fintype.prod_unique, show (default : Finset (Fin 0)) = ∅ from Subsingleton.elim _ _]; simp [cubeProduct]
  | succ d ih =>
    rw [← Fin.cons_self_tail h, prod_vertices_succ]
    simp only [cubeProduct, Fin.tail_cons, Fin.cons_zero, sum_lowerFace, sum_upperFace, ih, add_assoc]

/-- Tonelli for a finite family of disjoint coordinates with counting measure. -/
theorem tsum_pi_separated {G : Type*} [Countable G] (k : ℕ) (u : Fin k → G → ℝ≥0∞) :
    (∑' x : Fin k → G, ∏ i, u i (x i)) = ∏ i, ∑' x : G, u i x := by
  let : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  simpa only [cubeMeasure_count, lintegral_count] using lintegral_pi_separated
    (Measure.count : Measure G) k u (fun i => measurable_of_countable _)

/-- Counting-measure `U^(d,p)` raised to its integral degree is exactly
the unrestricted homogeneous configuration mass. -/
theorem gowers_count_nat_mass {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G] (d k : ℕ) (f : G → ℝ≥0) :
    (gowers Measure.count d (k+1:ℕ) f) ^ ((2:ℝ)^d*(k+1:ℕ)) =
      ∑' h : Fin d → G, (∑' x : G, cubeProduct d f h x)^(k+1) := by
  simp only [gowers,lp,autocorrelation,cubeMeasure_count,lintegral_count,← ENNReal.rpow_mul]
  have hp : (0:ℝ) < (k+1:ℕ) := by positivity
  rw [show 1/(k+1:ℕ)*(1/(2:ℝ)^d)*((2:ℝ)^d*(k+1:ℕ)) = 1 by field_simp]
  simp only [ENNReal.rpow_one, ENNReal.rpow_natCast]

end LpGowers.Discrete
