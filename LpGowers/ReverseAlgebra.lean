module

public import LpGowers.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Logarithmic rearrangement of the reverse weighted Hölder estimate in §5. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace LpGowers

theorem reverse_scalar {k : ℕ} (hk : 1 ≤ k) {p : ℝ} {q θ : Fin (k + 1) → ℝ}
    (hpar : DegreeParameters k p q θ) (hrev : DegreeReverse p θ)
    {N : Fin (k + 1) → ℝ} (hN : ∀ i, 0 < N i) {U : ℝ} (hU : 0 < U)
    (h : N 0 ≤ U ^ (1 / (θ 0 * p)) *
      (∏ i, N i ^ (1 / (k : ℝ))) ^ ((p - 1) / (θ 0 * p)) *
      ∏ j : Fin k, N j.succ ^ (-θ j.succ / θ 0)) :
    (∏ i, N i ^ (2 * p * θ i / q i)) ≤ U := by
  obtain ⟨hq, _, hrel⟩ := hpar
  obtain ⟨hp, ht, _⟩ := hrev
  change 0 < θ 0 at ht
  change ∀ i, (1 - 1 / p) / (k : ℝ) = θ i * (1 - 2 / q i) at hrel
  have hpp : 0 < p := by linarith
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have htp := mul_pos ht hpp
  let L := fun i => Real.log (N i)
  have hcoef (i : Fin (k + 1)) : 2 * p * θ i / q i = p * θ i - (p - 1) / (k : ℝ) := by
    have hh := hrel i
    field_simp [hk'.ne', hpp.ne', (hq i).ne'] at hh ⊢
    linarith
  have hlog {ι : Type} [Fintype ι] (B : ι → ℝ) (hB : ∀ i, 0 < B i) (e : ι → ℝ) :
      Real.log (∏ i, B i ^ e i) = ∑ i, e i * Real.log (B i) := by
    rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hB i) _).ne')]
    simp_rw [Real.log_rpow (hB _) _]
  apply (Real.log_le_log_iff (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hN i) _)) hU).mp
  rw [hlog N hN (fun i => 2 * p * θ i / q i)]
  simp_rw [hcoef, sub_mul, Finset.sum_sub_distrib, mul_assoc p, ← Finset.mul_sum]
  have hraw := Real.log_le_log (hN 0) h
  have hprod : 0 < ∏ i, N i ^ (1 / (k : ℝ)) := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hN i) _)
  have hother : 0 < ∏ j : Fin k, N j.succ ^ (-θ j.succ / θ 0) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hN _) _)
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hprod _)).ne' hother.ne',
    Real.log_mul (Real.rpow_pos_of_pos hU _).ne' (Real.rpow_pos_of_pos hprod _).ne',
    Real.log_rpow hU, Real.log_rpow hprod, hlog N hN (fun _ => 1 / (k : ℝ)),
    hlog (fun j : Fin k => N j.succ) (fun j => hN j.succ) (fun j => -θ j.succ / θ 0)] at hraw
  change p * (∑ i, θ i * L i) - ((p - 1) / ↑k) * ∑ i, L i ≤ _
  have hsum : (∑ j : Fin k, (-θ j.succ / θ 0) * L j.succ) =
      (-1 / θ 0) * ∑ j : Fin k, θ j.succ * L j.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change L 0 ≤ 1 / (θ 0 * p) * Real.log U +
    ((p - 1) / (θ 0 * p)) * (∑ i, 1 / (k : ℝ) * L i) +
    ∑ j : Fin k, (-θ j.succ / θ 0) * L j.succ at hraw
  rw [← Finset.mul_sum, hsum] at hraw
  rw [Fin.sum_univ_succ (fun i => θ i * L i)]
  field_simp [ht.ne', hpp.ne', hk'.ne'] at hraw ⊢
  nlinarith only [hraw]

end LpGowers
