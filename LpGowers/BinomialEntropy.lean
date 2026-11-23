module

public import LpGowers.Discrete
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Strict decrease of the binomial entropy per fair bit

The entropy of the binomial law is l bits minus the mean logarithmic size of
a Hamming layer. The one-step comparison of layer sizes follows just by
testing one probability in a binomial distribution. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Real
namespace LpGowers.Discrete

private def binLog (n k : ℕ) : ℝ := log (n.choose k)
private def meanLayerLog (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*binLog n k) / (2:ℝ)^n

private theorem real_choose_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) = 2^n := by exact_mod_cast Nat.sum_range_choose n

private theorem entropy_eq_layerLog (n : ℕ) :
    binomialEntropy n = n - meanLayerLog n / log 2 := by
  let C (k : ℕ) : ℝ := n.choose k
  have hw : ∑ k ∈ Finset.range (n+1), C k = 2^n := real_choose_sum n
  have he (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      C k/2^n * logTwo (C k/2^n) = ((C k*binLog n k) - C k*(n*log 2))/(2^n*log 2) := by
    have hC : 0 < C k := by dsimp [C]; exact_mod_cast Nat.choose_pos (by simpa using hk)
    rw [logTwo, Real.logb, Real.log_div hC.ne' (by positivity), Real.log_pow]
    dsimp [C,binLog]
    field_simp
  change -(∑ k ∈ Finset.range (n+1), C k/2^n * logTwo (C k/2^n)) = _
  rw [Finset.sum_congr rfl he, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hw]
  dsimp [meanLayerLog,C]
  field_simp
  ring

/-- For 0<k<N, the k-th atom of Binomial(N,k/N) has mass strictly below 1. -/
private theorem choose_atom_lt_one (N k : ℕ) (hk : 0 < k) (hN : k < N) :
    (N.choose k : ℝ)*((k:ℝ)/N)^k * ((N-k:ℕ)/ (N:ℝ))^(N-k) < 1 := by
  let a := (k:ℝ)/N
  let b := ((N-k:ℕ):ℝ)/N
  have hn : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have ha : 0 < a := div_pos (by exact_mod_cast hk) hn
  have hb : 0 < b := div_pos (by exact_mod_cast (by omega : 0 < N-k)) hn
  have hab : a+b = 1 := by dsimp [a,b]; rw [Nat.cast_sub hN.le]; field_simp; ring
  let term (j : ℕ) : ℝ := (N.choose j) * a^j * b^(N-j)
  have hmass : ∑ j ∈ Finset.range (N+1), term j = 1 := by
    have hh := add_pow a b N
    rw [hab, one_pow] at hh
    simpa [term,mul_assoc,mul_left_comm,mul_comm] using hh.symm
  have hsmall : ({k,0} : Finset ℕ) ⊆ Finset.range (N+1) := by
    intro j hj
    simp at hj ⊢
    omega
  have hle : term k + term 0 ≤ 1 := by
    rw [← hmass]
    simpa [Finset.sum_insert, hk.ne'] using
      (Finset.sum_le_sum_of_subset_of_nonneg (f := term) hsmall (by intro j _ _; dsimp [term]; positivity))
  have h0 : 0 < term 0 := by dsimp [term]; simp; positivity
  exact (lt_add_of_pos_right _ h0).trans_le hle

/-- Logarithmic layer comparison for interior Hamming weights. -/
private theorem log_layer_strict (n k : ℕ) (hk : 0 < k) (hk' : k ≤ n) :
    (n+1-k : ℕ)*binLog n k + (k:ℝ)*binLog n (k-1) < (n:ℝ)*binLog (n+1) k := by
  let N := n+1
  let C : ℝ := N.choose k
  let a := (k:ℝ)/N
  let b := ((N-k:ℕ):ℝ)/N
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hkN : k < N := by dsimp [N]; omega
  have ha : 0 < a := div_pos (by exact_mod_cast hk) hN
  have hb : 0 < b := div_pos (by exact_mod_cast (by omega : 0 < N-k)) hN
  have hc : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos hkN.le
  have hbefore : (n.choose (k-1) : ℝ) = C*a := by
    dsimp [C,a,N]
    rw [← mul_div_assoc, eq_div_iff (by positivity)]
    exact_mod_cast (by
      have H := Nat.add_one_mul_choose_eq n (k-1)
      rw [Nat.sub_add_cancel hk] at H
      simpa [Nat.mul_comm] using H : n.choose (k-1)*(n+1) = (n+1).choose k*k)
  have hat : (n.choose k : ℝ) = C*b := by
    dsimp [C,b,N]
    rw [← mul_div_assoc, eq_div_iff (by positivity)]
    exact_mod_cast Nat.choose_mul_succ_eq n k
  have hh : log C + k*log a + (N-k:ℕ)*log b < 0 := by
    have H := Real.log_neg (show 0 < C*a^k*b^(N-k) by positivity) (choose_atom_lt_one N k hk hkN)
    simpa [Real.log_mul (by positivity : C*a^k ≠ 0) (by positivity : b^(N-k) ≠ 0),
      Real.log_mul hc.ne' (by positivity : a^k ≠ 0), Real.log_pow] using H
  change ((N-k:ℕ):ℝ)*log (n.choose k) + k*log (n.choose (k-1)) < n*log C
  rw [hat, hbefore, Real.log_mul hc.ne' hb.ne', Real.log_mul hc.ne' ha.ne']
  have hnk : ((N-k:ℕ):ℝ) = n+1-k := by rw [Nat.cast_sub hkN.le]; simp [N]
  rw [hnk] at hh ⊢
  linarith



private theorem binomialEntropy_normalized_succ (n : ℕ) (hn : 0<n) :
    binomialEntropy (n+1)/(n+1:ℕ) < binomialEntropy n/n := by
  let T (k : ℕ) : ℝ := (n.choose k)*binLog n k
  let U (k : ℕ) : ℝ := ((n+1).choose k)*binLog (n+1) k
  let prev (k : ℕ) : ℝ := if k=0 then 0 else T (k-1)
  let A (k : ℕ) : ℝ := (n+1)*(T k + prev k)
  let B (k : ℕ) : ℝ := n * U k
  have hpoint (k : ℕ) (hk : 0<k) (hk' : k ≤ n) : A k < B k := by
    have H := log_layer_strict n k hk hk'
    let C : ℝ := (n+1).choose k
    have hc : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos (by omega : k ≤ n+1)
    have ht : (n+1 : ℝ)*(n.choose k:ℝ) = C*((n+1-k:ℕ):ℝ) := by
      dsimp [C]
      exact_mod_cast (by simpa [Nat.mul_comm] using Nat.choose_mul_succ_eq n k)
    have hu : (n+1 : ℝ)*(n.choose (k-1):ℝ) = C*k := by
      dsimp [C]
      have he := Nat.add_one_mul_choose_eq n (k-1)
      rw [Nat.sub_add_cancel hk] at he
      exact_mod_cast he
    have H' := mul_lt_mul_of_pos_left H hc
    dsimp [A,B,T,U,prev]
    simp only [hk.ne', ite_false]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ht, hu]
    dsimp [C] at H' ⊢
    linarith
  have hsum : ∑ k ∈ Finset.range (n+2), A k < ∑ k ∈ Finset.range (n+2), B k := by
    apply Finset.sum_lt_sum
    · intro k hk
      have hkn : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
      by_cases h0 : k=0
      · simp [h0,A,B,T,U,prev,binLog]
      by_cases he : k=n+1
      · simp [he,A,B,T,U,prev,binLog]
      exact (hpoint k (Nat.pos_of_ne_zero h0) (by omega)).le
    · exact ⟨1, Finset.mem_range.mpr (by omega), hpoint 1 (by decide) hn⟩
  have hprev : ∑ k ∈ Finset.range (n+2), prev k = ∑ k ∈ Finset.range (n+1), T k := by
    rw [Finset.sum_range_succ']
    simp [prev]
  have hT : ∑ k ∈ Finset.range (n+2), T k = ∑ k ∈ Finset.range (n+1), T k := by
    rw [Finset.sum_range_succ]
    simp [T]
  change (∑ k ∈ Finset.range (n+2), (n+1 : ℝ)*(T k+prev k)) <
    ∑ k ∈ Finset.range (n+2), (n:ℝ)*U k at hsum
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hprev, hT] at hsum
  rw [entropy_eq_layerLog, entropy_eq_layerLog]
  dsimp [meanLayerLog]
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  push_cast
  field_simp
  rw [pow_succ]
  dsimp [T,U] at hsum
  nlinarith only [mul_lt_mul_of_pos_right hsum (show (0:ℝ)<2^n by positivity)]

/-- Strict entropy decrease per summand, Beker–Crmarić–Kovač Corollary 7.
This proof uses binomial probabilities instead of asymptotic estimates. -/
theorem binomialEntropy_div_strict {l n : ℕ} (hl : 0<l) (hn : l<n) :
    binomialEntropy n/n < binomialEntropy l/l := by
  induction n, hn using Nat.le_induction with
  | base => exact binomialEntropy_normalized_succ l hl
  | succ k hk ih => exact (binomialEntropy_normalized_succ k (by omega)).trans ih

end LpGowers.Discrete
