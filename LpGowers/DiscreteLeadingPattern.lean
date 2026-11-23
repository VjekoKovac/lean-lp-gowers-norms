module

public import LpGowers.DiscretePatternBounds
import Mathlib.Tactic

/-! # The dominant, all-unit group of increment patterns

The maximal-rank contribution is bounded with its exact multiplicity. This
preserves the additive constant term of the asymptotic expansion. -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Pointwise
namespace LpGowers.Discrete

/-- At maximal active rank, the signs determine every step. The magnitude is
one and the base is forced by the length of the interval. -/
theorem activePatterns_card_le (l : ℕ) : (activePatterns (l+1) l).card ≤ 2^l := by
  let code := fun z : (Fin l → Lattice 1) × Lattice 1 => fun i => decide (0 < z.1 i 0)
  have H : (activePatterns (l+1) l).card ≤ (Finset.univ : Finset (Fin l → Bool)).card := by
    apply Finset.card_le_card_of_injOn code (fun _ _ => Finset.mem_univ _)
    intro z hz w hw he
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have zstep := (Finset.mem_product.mp hz'.1).1
    have wstep := (Finset.mem_product.mp hw'.1).1
    have hs : z.1 = w.1 := by
      funext i j
      rw [Fin.eq_zero j]
      have hi := congrFun he i
      change decide (0 < z.1 i 0) = decide (0 < w.1 i 0) at hi
      rcases leading_unit zstep hz'.2 i with h | h <;>
        rcases leading_unit wstep hw'.2 i with h' | h' <;> simp_all
    exact Prod.ext hs (leading_origin zstep hz'.2 (hs ▸ hw'.2))
  simpa using H

private theorem unique_sum_power {X : Type*} (A : Finset X) (u : X → ℝ≥0) {p : ℕ}
    (hp : 0<p) (hu : ∀ a ∈ A, ∀ b ∈ A, u a ≠ 0 → u b ≠ 0 → a=b) :
    (∑ a ∈ A,u a)^p = ∑ a ∈ A,u a^p := by
  by_cases h : ∃ a∈A, u a ≠ 0
  · obtain ⟨a,ha,hn⟩ := h
    have hzero (b) (hb : b∈A) (hne : b≠a) : u b=0 := by
      by_contra hn'
      exact hne (hu b hb a ha hn' hn)
    rw [Finset.sum_eq_single_of_mem a ha hzero, Finset.sum_eq_single_of_mem a ha (fun b hb hba =>
      by rw [hzero b hb hba,zero_pow hp.ne'])]
  · push Not at h
    rw [Finset.sum_eq_zero h,zero_pow hp.ne']
    exact (Finset.sum_eq_zero fun a ha => by rw [h a ha, zero_pow hp.ne']).symm

/-- Unlike the lower ranks, the leading rank has no cardinality loss when
passing the integer power through the sum over origins. -/
theorem activeSum_leading (l d p : ℕ) (hld : l≤d) (hp : 0<p) (t : ℝ)
    (g : ℤ → ℝ≥0) (f : Lattice 1 → ℝ≥0) (hzero : ∀ x ∉ box 1 (l+1), f x=0)
    (hf : ∀ x ∈ box 1 (l+1), f x = g (x 0) ^ (t / ((2:ℝ)^d*p))) :
    activeSum (box 1 (l+1)) ((box 1 (l+1)-box 1 (l+1)).erase 0) p l (d-l) f =
      ∑ z ∈ activePatterns (l+1) l,
        ∏ S : Finset (Fin l), g (z.2 0 + ∑ i ∈ S, z.1 i 0) ^ (t / (2:ℝ)^l) := by
  classical
  let A := box 1 (l+1)
  let W := fun (h : Fin l → Lattice 1) (x : Lattice 1) => finiteCubeProduct l f h x ^ (2^(d-l))
  change (∑ h ∈ stepPool (l+1) l, (∑ x∈A,W h x)^p) = _
  calc
    _ = ∑ h ∈ stepPool (l+1) l, ∑ x∈A,(W h x)^p := by
      apply Finset.sum_congr rfl
      intro h hh
      apply unique_sum_power A _ hp
      intro a _ b _ ha hb
      exact leading_origin hh (finiteCubeProduct_fits hzero l h a (fun h => ha (by simp [W,h])))
        (finiteCubeProduct_fits hzero l h b (fun h => hb (by simp [W,h])))
    _ = _ := by
      rw [← Finset.sum_product']
      unfold activePatterns
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : fits A z.1 z.2
      · rw [ite_eq_left hz]
        exact pattern_cube_power hld hp t g f hf hz
      · rw [ite_eq_right hz]
        have Z : finiteCubeProduct l f z.1 z.2 = 0 := not_ne_iff.mp fun hnz =>
          hz (finiteCubeProduct_fits hzero l z.1 z.2 hnz)
        simp [W,Z,zero_pow hp.ne']

end LpGowers.Discrete
