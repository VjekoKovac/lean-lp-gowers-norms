module

public import LpGowers.DiscretePatterns
import Mathlib.Tactic

/-! # Bounds for each active-rank contribution

In the maximal active rank the fitting origin is unique and all directions are
unit signs. Lower ranks use a finite sum bound before the fair-bit monomials
are estimated by entropy. -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Pointwise
namespace LpGowers.Discrete

private theorem finite_vertices {G : Type*} [AddCommGroup G] (l : ℕ) (f : G → ℝ≥0)
    (h : Fin l → G) (x : G) :
    finiteCubeProduct l f h x = ∏ S : Finset (Fin l), f (x+∑ i∈S,h i) := by
  induction l generalizing x with
  | zero =>
    rw [Fintype.prod_unique,show (default : Finset (Fin 0))=∅ from Subsingleton.elim _ _]
    simp [finiteCubeProduct]
  | succ l ih =>
    rw [← Fin.cons_self_tail h,prod_vertices_succ]
    simp only [finiteCubeProduct,Fin.tail_cons,Fin.cons_zero,sum_lowerFace,sum_upperFace,ih,add_assoc]

private theorem sum_pow_card {X : Type*} (A : Finset X) (u : X → ℝ≥0) (p : ℕ) (hp : 0 < p) :
    (∑ x∈A,u x)^p ≤ (A.card:ℝ≥0)^(p-1) * ∑ x ∈ A, u x^p := by
  have h : 1 ≤ (p:ℝ) := by exact_mod_cast hp
  have cast : (p:ℝ)-1 = ((p-1:ℕ):ℝ) := by rw [Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one]
  simpa only [cast,NNReal.rpow_natCast] using
    NNReal.rpow_sum_le_const_mul_sum_rpow A u h

/-- The monomial produced by a fitting compressed pattern after taking the
outer positive integer power. -/
theorem pattern_cube_power {n d l p : ℕ} (hld : l ≤ d) (hp : 0 < p)
    (t : ℝ) (g : ℤ → ℝ≥0) (f : Lattice 1 → ℝ≥0)
    (hf : ∀ x ∈ box 1 n, f x = g (x 0) ^ (t / ((2:ℝ)^d*p)))
    {z : (Fin l → Lattice 1) × Lattice 1} (hz : fits (box 1 n) z.1 z.2) :
    (finiteCubeProduct l f z.1 z.2 ^ (2^(d-l)))^p =
      ∏ S : Finset (Fin l), g (z.2 0 + ∑ i ∈ S, z.1 i 0) ^ (t / (2:ℝ)^l) := by
  rw [finite_vertices,← Finset.prod_pow,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro S _
  rw [hf _ (hz S)]
  simp only [Pi.add_apply, Finset.sum_apply, ← NNReal.rpow_mul_natCast]
  congr 1
  push_cast
  have he : (2:ℝ)^(d-l)*2^l=2^d := by rw [← pow_add,Nat.sub_add_cancel hld]
  have hp' : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  field_simp
  nlinarith only [congrArg (fun z : ℝ => t*z) he]

/-- Ranks below the largest possible rank are bounded by finitely many entropy
monomials with a coefficient depending only on the side and the outer power. -/
theorem activeSum_middle {n d l p : ℕ} (hld : l≤d) (hp : 0<p)
    (t : ℝ) (g : ℤ → ℝ≥0) (f : Lattice 1 → ℝ≥0)
    (hzero : ∀ x ∉ box 1 n, f x=0)
    (hf : ∀ x ∈ box 1 n, f x = g (x 0) ^ (t / ((2:ℝ)^d*p))) :
    activeSum (box 1 n) ((box 1 n-box 1 n).erase 0) p l (d-l) f ≤
      (n:ℝ≥0)^(p-1) * ∑ z ∈ activePatterns n l,
        ∏ S : Finset (Fin l), g (z.2 0 + ∑ i ∈ S, z.1 i 0) ^ (t/(2:ℝ)^l) := by
  classical
  let A := box 1 n
  let W := fun (h : Fin l → Lattice 1) (x : Lattice 1) => finiteCubeProduct l f h x ^ (2^(d-l))
  have hbound (h : Fin l → Lattice 1) : (∑ x∈A, W h x)^p ≤
      (n:ℝ≥0)^(p-1) * ∑ x∈A, (W h x)^p := by simpa [A,card_box] using sum_pow_card A (W h) p hp
  change (∑ h ∈ stepPool n l, (∑ x∈A,W h x)^p) ≤ _
  apply (Finset.sum_le_sum (fun h _ => hbound h)).trans_eq
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_product']
  unfold activePatterns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : fits A z.1 z.2
  · rw [ite_eq_left hz]
    exact pattern_cube_power hld hp t g f hf hz
  · rw [ite_eq_right hz]
    have Z : finiteCubeProduct l f z.1 z.2 = 0 := not_ne_iff.mp fun hnz => hz (finiteCubeProduct_fits hzero l z.1 z.2 hnz)
    simp [W,Z,zero_pow hp.ne']

/-- No fitting cube can have as many active steps as there are lattice points. -/
theorem activeSum_vanish {n l p : ℕ} (hnl : n ≤ l) (hp : 0 < p) (r : ℕ) (f : Lattice 1 → ℝ≥0)
    (hf : ∀ x ∉ box 1 n, f x = 0) :
    activeSum (box 1 n) ((box 1 n-box 1 n).erase 0) p l r f = 0 := by
  apply Finset.sum_eq_zero
  intro h hh
  change h ∈ stepPool n l at hh
  have H (x : Lattice 1) : finiteCubeProduct l f h x = 0 := by
    by_contra hn
    have hl := pattern_span (finiteCubeProduct_fits hf l h x hn)
    have hL := active_count_le_span hh
    omega
  simp [H, zero_pow hp.ne']

end LpGowers.Discrete
