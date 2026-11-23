module

public import LpGowers.DiscreteEntropyTest
public import LpGowers.DiscreteTriangle
public import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Tactic

/-! # Binomial entropy lower bound

The one-dimensional test in §8 is the `q`th root of the Binomial(l,1/2)
mass function. The signed increment count cancels the parameter `p` after
passing to the dual exponent. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal BigOperators Topology
namespace LpGowers.Discrete

private def prob (l j : ℕ) : ℝ≥0 := (l.choose j : ℝ≥0) / 2^l

private theorem prob_pos {l j : ℕ} (hj : j ≤ l) : 0 < prob l j := by
  dsimp [prob]; apply div_pos (by exact_mod_cast Nat.choose_pos hj) (by positivity)

private theorem prob_sum (l : ℕ) : (∑ j ∈ Finset.range (l+1), prob l j) = 1 := by
  rw [show (∑ j ∈ Finset.range (l+1), prob l j) = (∑ j ∈ Finset.range (l+1), (l.choose j : ℝ≥0))/2^l by rw [Finset.sum_div];rfl]
  have H : (∑ j ∈ Finset.range (l+1), (l.choose j : ℝ≥0)) = (2:ℝ≥0)^l := by exact_mod_cast Nat.sum_range_choose l
  rw [H,div_self (by positivity)]

private theorem oneDim_sum (l : ℕ) (g : Lattice 1 → ℝ≥0) :
    (∑ x ∈ box 1 (l+1), g x) = ∑ j ∈ Finset.range (l+1), g (fun _ => (j:ℤ)) := by
  apply Finset.sum_bij' (fun (x : Lattice 1) _ => (x 0).toNat) (fun (j : ℕ) _ (_ : Fin 1) => (j:ℤ))
  · intro x hx
    have h := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx 0)
    apply Finset.mem_range.mpr
    omega
  · intro j hj
    apply Fintype.mem_piFinset.mpr
    intro i
    have h := Finset.mem_range.mp hj
    exact Finset.mem_Ico.mpr ⟨by positivity,by exact_mod_cast h⟩
  · intro x hx
    funext i
    have h := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx 0)
    rw [Fin.eq_zero i, Int.toNat_of_nonneg h.1]
  · intro j _; simp
  · intro x hx
    congr 1
    funext i
    have h := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx 0)
    rw [Fin.eq_zero i,Int.toNat_of_nonneg h.1]

/-- Explicit finite-degree entropy test against every admissible functional
exponent. This conclusion is independent of critical-product duality. -/
theorem entropy_functional_test (d k l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d) {q : ℝ}
    (hadm : q ∈ functionExponents d (k+1) (l+1)) :
    logTwo ((d.choose l * 2^l : ℕ) : ℝ) ≤
      ((2:ℝ)^d * (k+1:ℕ) / q) * binomialEntropy l := by
  classical
  have hq := hadm.1
  let B := box 1 (l+1)
  let f := fun x : Lattice 1 => if x∈B then (prob l (x 0).toNat)^(1/q) else 0
  have hsupport (x) (hx : x ∉ B) : f x=0 := by simp [f,hx]
  have hfj {j : ℕ} (hj : j ∈ Finset.range (l+1)) :
      f (fun _ => (j:ℤ)) = (prob l j)^(1/q) := by
    have hB : (fun _ : Fin 1 => (j:ℤ)) ∈ B := by
      apply Fintype.mem_piFinset.mpr
      intro _
      exact Finset.mem_Ico.mpr ⟨by positivity,by exact_mod_cast Finset.mem_range.mp hj⟩
    simp [f,hB]
  have hsum : (∑ x ∈ B, (f x)^q) = 1 := by
    rw [oneDim_sum l (fun x => (f x)^q)]
    apply Eq.trans _ (prob_sum l)
    apply Finset.sum_congr rfl
    intro j hj
    rw [hfj hj, ← NNReal.rpow_mul, one_div_mul_cancel hq.ne',NNReal.rpow_one]
  have hU := (bound_iff_weightedEnergy d k (l+1) 1 hq f hsupport).mp (hadm.2 1 f hsupport)
  change weightedEnergy d (k+1) B f ≤ (∑ x ∈ B, (f x)^q)^_ at hU
  rw [hsum,NNReal.one_rpow] at hU
  let C := d.choose l * 2^l
  let W := binomialProduct f l 0
  have hCW : (C:ℝ≥0) * (W^(2^(d-l)))^(k+1) ≤ 1 := (signed_weightedEnergy_lower d l (k+1) hl f).trans hU
  have hC : (0:ℝ) < C := by
    dsimp [C]; exact_mod_cast Nat.mul_pos (Nat.choose_pos hld) (show 0 < 2^l by positivity)
  have hp (j) (hj : j∈Finset.range (l+1)) : 0 < prob l j := prob_pos (by have := Finset.mem_range.mp hj; omega)
  have hW : 0 < W := by
    apply Finset.prod_pos
    intro j hj
    simp only [zero_add]
    rw [hfj hj]
    exact pow_pos (NNReal.rpow_pos (hp j hj)) _
  have hCW' : (C:ℝ) * ((W:ℝ)^(2^(d-l)))^(k+1) ≤ 1 := by exact_mod_cast hCW
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (mul_pos hC (pow_pos (pow_pos (show 0 < (W:ℝ) by exact_mod_cast hW) _) _)) hCW'
  rw [Real.logb_one, Real.logb_mul hC.ne' (by positivity), Real.logb_pow, Real.logb_pow] at hlog
  have hP : Real.logb 2 (W:ℝ) = -((2:ℝ)^l/q) * binomialEntropy l := by
    have hW' : (W:ℝ) = ∏ j ∈ Finset.range (l+1), ((prob l j : ℝ)^(1/q))^(l.choose j) := by
      dsimp only [W,binomialProduct]
      rw [NNReal.coe_prod]
      apply Finset.prod_congr rfl
      intro j hj
      simp only [zero_add,hfj hj,NNReal.coe_pow,NNReal.coe_rpow]
    rw [hW',Real.logb_prod _ _ (fun j hj => (pow_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast hp j hj) _) _).ne')]
    simp only [Real.logb_pow]
    unfold binomialEntropy
    rw [neg_mul_neg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hp j hj)]
    dsimp [prob,logTwo]
    push_cast
    field_simp
  rw [hP] at hlog
  have two : (2:ℝ)^(d-l) * 2^l = 2^d := by rw [← pow_add,Nat.sub_add_cancel hld]
  change Real.logb 2 C ≤ _
  push_cast at hlog ⊢
  field_simp [hq.ne'] at hlog ⊢
  nlinarith only [hlog,congrArg (fun z : ℝ => z*((k:ℝ)+1)*binomialEntropy l) two]

/-- The symmetric binomial entropy is strictly positive for every positive
number of trials. -/
theorem binomialEntropy_pos {l : ℕ} (hl : 1 ≤ l) : 0 < binomialEntropy l := by
  let w := fun j => ((prob l j):ℝ)
  have hpos (j) (hj : j∈Finset.range (l+1)) : 0 < w j := by
    exact_mod_cast prob_pos (by have := Finset.mem_range.mp hj; omega : j ≤ l)
  have hle (j) (hj : j∈Finset.range (l+1)) : w j ≤ 1 := by
    have H := (Finset.single_le_sum (f := prob l) (fun _ _ => zero_le) hj).trans_eq (prob_sum l)
    exact_mod_cast H
  have hn : 0∈Finset.range (l+1) := by simp
  have hw : w 0 < 1 := by
    dsimp [w,prob]
    push_cast
    simp only [Nat.choose_zero_right,Nat.cast_one]
    exact (div_lt_one (by positivity)).2 (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega))
  have hsum : 0 < ∑ j ∈ Finset.range (l+1), -(w j * Real.logb 2 (w j)) := by
    apply Finset.sum_pos'
    · exact fun j hj => neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hpos j hj).le
        (Real.logb_nonpos (by norm_num) (hpos j hj).le (hle j hj)))
    · exact ⟨0,hn,neg_pos.mpr (mul_neg_of_pos_of_neg (hpos 0 hn)
        (Real.logb_neg (by norm_num) (hpos 0 hn) hw))⟩
  simpa [w,prob,binomialEntropy,logTwo,Finset.sum_neg_distrib] using hsum

/-- The logarithmic remainder in replacing the binomial coefficient by its
leading monomial tends to zero at fixed rank. Uses Mathlib's
`isEquivalent_choose` (Mitchell Horner). -/
theorem signed_count_log_remainder (l : ℕ) :
    Tendsto (fun d : ℕ => logTwo ((d.choose l * 2^l : ℕ) : ℝ) -
      ((l:ℝ)*logTwo (2*(d:ℝ))-logTwo l.factorial)) atTop (𝓝 0) := by
  have hden : ∀ᶠ d : ℕ in atTop, (d:ℝ)^l / (l.factorial:ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hd' : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
    positivity
  have H := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp (isEquivalent_choose l)
  have HH := (Real.continuousAt_logb (b := (2:ℝ)) (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp H
  simp only [Real.logb_one] at HH
  apply HH.congr'
  filter_upwards [eventually_ge_atTop (max 1 l)] with d hd
  have hd' : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hc : 0 < (d.choose l:ℝ) := by exact_mod_cast Nat.choose_pos (show l ≤ d by omega)
  have hfac : 0 < (l.factorial:ℝ) := by positivity
  change Real.logb 2 ((d.choose l : ℝ) / ((d:ℝ)^l / l.factorial)) = _
  rw [Real.logb_div hc.ne' (div_pos (pow_pos hd' l) hfac).ne',
    Real.logb_div (pow_pos hd' l).ne' hfac.ne']
  simp only [logTwo,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,
    Real.logb_mul hc.ne' (by positivity : (2:ℝ)^l ≠ 0), Real.logb_pow,
    Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hd'.ne',Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
  ring

/-- Additive-error large-degree lower estimate for the dual functional
exponent. This follows unconditionally from the one-dimensional test. -/
theorem entropy_largeDegree_lower_functional (k l : ℕ) (hl : 1 ≤ l) {η : ℝ} (hη : 0<η) :
    ∀ᶠ d : ℕ in atTop, largeDegreeMainTerm (l+1) d - η ≤
      (2:ℝ)^d * (k+1:ℕ) / criticalQ d (k+1) (l+1) := by
  have hH := binomialEntropy_pos hl
  have H := (signed_count_log_remainder l).eventually (lt_mem_nhds (show -(η * binomialEntropy l)<0 by exact neg_neg_of_pos (mul_pos hη hH)))
  filter_upwards [H,eventually_ge_atTop l] with d hd hld
  have bound := entropy_functional_test d k l hl hld (criticalQ_isGreatest d k (l+1) (by omega)).1
  change -(η * binomialEntropy l) < logTwo ((d.choose l * 2^l : ℕ) : ℝ) -
      ((l:ℝ)*logTwo (2*(d:ℝ))-logTwo l.factorial) at hd
  change ((l:ℝ)*logTwo (2*(d:ℝ))-logTwo l.factorial)/binomialEntropy l - η ≤ _
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hH).mpr
  nlinarith only [bound,hd]

/-- Lower half of Theorem 1.5(c), for every fixed side length and power,
with additive error tending to zero. -/
theorem entropy_largeDegree_lower (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, largeDegreeMainTerm n d - η ≤ criticalT d p n := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  filter_upwards [entropy_largeDegree_lower_functional k l (by omega) hη] with d hd
  have hq := (criticalQ_isGreatest d k (l+1) hn).1.1
  have hpq := critical_product d k (l+1) hn
  rw [← hpq,mul_comm,mul_div_cancel_right₀ _ hq.ne'] at hd
  exact hd

end LpGowers.Discrete
