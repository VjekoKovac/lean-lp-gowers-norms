module

public import LpGowers.DiscreteEntropyLower
public import LpGowers.BinomialEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! # Large-degree rates for the discrete entropy upper bound -/

@[expose] public section
noncomputable section
open Filter Real
open scoped Topology BigOperators NNReal
namespace LpGowers.Discrete

private theorem affineMainTerm (N d : ℕ) (hd : 0<d) (δ : ℝ) :
    largeDegreeMainTerm (N+1) d + δ =
      ((N:ℝ)/binomialEntropy N)*logTwo d +
        (((N:ℝ)-logTwo (N.factorial))/binomialEntropy N+δ) := by
  unfold largeDegreeMainTerm logTwo
  simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
  rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) (show (d:ℝ) ≠ 0 by exact_mod_cast hd.ne'), Real.logb_self_eq_one (by norm_num)]
  ring

/-- The trial exponent in §8 grows without bound with the degree. -/
theorem entropyMainTerm_tendsto (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    Tendsto (fun d : ℕ => largeDegreeMainTerm (N+1) d + δ) atTop atTop := by
  have ha : 0 < (N:ℝ)/binomialEntropy N := div_pos (by exact_mod_cast hN) (binomialEntropy_pos hN)
  have hL := (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp tendsto_natCast_atTop_atTop
  have h := tendsto_atTop_add_const_right _ (((N:ℝ)-logTwo N.factorial)/binomialEntropy N+δ) (hL.const_mul_atTop ha)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  exact (affineMainTerm N d hd δ).symm

private theorem power_log_identity {x a b K : ℝ} (hx : 0<x) :
    (2:ℝ)^(-K * (a*logTwo x+b)) = 2^(-K*b)*x^(-K*a) := by
  rw [show -K*(a*logTwo x+b) = -K*b+logTwo x*(-K*a) by ring, Real.rpow_add (by norm_num),
    Real.rpow_mul (by norm_num : 0≤(2:ℝ)) (logTwo x) (-K*a)]
  congr 2
  exact Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hx

/-- Dimension-polynomial weights are dominated by the exponential entropy
bound whenever the entropy-per-step inequality is strict. -/
theorem entropy_rate_zero (N : ℕ) (δ l K : ℝ) (hlt : l < K*((N:ℝ)/binomialEntropy N)) :
    Tendsto (fun d : ℕ => (d:ℝ)^l*2^(-K*(largeDegreeMainTerm (N+1) d+δ))) atTop (𝓝 0) := by
  let a := (N:ℝ)/binomialEntropy N
  let b := ((N:ℝ)-logTwo N.factorial)/binomialEntropy N + δ
  have hdeg : 0 < K*a-l := sub_pos.mpr hlt
  have hdec := (tendsto_rpow_neg_atTop hdeg).comp tendsto_natCast_atTop_atTop
  have hscaled := hdec.const_mul ((2:ℝ)^(-K*b))
  rw [mul_zero] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  rw [affineMainTerm N d hd δ, power_log_identity hd', mul_left_comm]
  change _ = 2^(-K*b)*((d:ℝ)^l*(d:ℝ)^(-K*a))
  rw [← Real.rpow_add hd']
  change (2:ℝ)^(-K*b)*(d:ℝ)^(-(K*a-l)) = 2^(-K*b)*(d:ℝ)^(l+-K*a)
  rw [show -(K*a-l) = l+-K*a by ring]

theorem entropy_minor_rate (N l : ℕ) (hl : 1 ≤ l) (hlN : l<N) (δ : ℝ) :
    Tendsto (fun d : ℕ => (d:ℝ)^l*2^(-binomialEntropy l*(largeDegreeMainTerm (N+1) d+δ))) atTop (𝓝 0) := by
  have H := binomialEntropy_div_strict hl hlN
  have hN : 0 < (N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hL : 0 < (l:ℝ) := by exact_mod_cast hl
  have hn := binomialEntropy_pos (show 1 ≤ N by omega)
  have hlt : (l:ℝ) < binomialEntropy l*((N:ℝ)/binomialEntropy N) := by
    rw [← mul_div_assoc, lt_div_iff₀ hn]
    exact (by nlinarith only [(div_lt_div_iff₀ hN hL).mp H])
  simpa only [Real.rpow_natCast] using entropy_rate_zero N δ l (binomialEntropy l) hlt

/-- The dominant signed-unit patterns have total coefficient at most
2^(-H*δ), strictly less than one at every positive δ. -/
theorem entropy_leading_rate (N d : ℕ) (hN : 1 ≤ N) (hd : 0<d) (δ : ℝ) :
    (d.choose N : ℝ)*2^N*2^(-binomialEntropy N*(largeDegreeMainTerm (N+1) d+δ)) ≤ 2^(-binomialEntropy N*δ) := by
  let H := binomialEntropy N
  have hH : 0 < H := binomialEntropy_pos hN
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hD : 0 < 2*(d:ℝ) := by positivity
  have hfac : 0 < (N.factorial:ℝ) := by exact_mod_cast N.factorial_pos
  have he : -H*(largeDegreeMainTerm (N+1) d+δ) =
      -H*δ + logTwo N.factorial - logTwo ((2*(d:ℝ))^N) := by
    simp only [largeDegreeMainTerm, Nat.add_sub_cancel, logTwo, Real.logb_pow]
    dsimp [H] at hH ⊢
    field_simp
    ring
  change _*_*(2:ℝ)^(-H*_) ≤ _
  rw [he, Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num), logTwo, logTwo, Nat.cast_ofNat,
    Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) (pow_pos hD _),
    Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hfac, mul_pow]
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div N d) (by positivity)) (by positivity))
  dsimp [H]
  field_simp
  ring_nf
  norm_num

/-- An explicit small threshold makes the total concentrated-case remainder
decay, even after multiplying by d^N. -/
theorem exists_entropy_threshold (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    ∃ θ : ℝ≥0, 0<θ ∧ θ<1 ∧ Tendsto (fun d : ℕ =>
      (d:ℝ)^N * (θ:ℝ)^((largeDegreeMainTerm (N+1) d+δ)/(2:ℝ)^N-1)) atTop (𝓝 0) := by
  let a := (N:ℝ)/binomialEntropy N
  have ha : 0 < a := div_pos (by exact_mod_cast hN) (binomialEntropy_pos hN)
  let K := ((N:ℝ)+1)/a
  have hK : 0 < K := div_pos (by positivity) ha
  let c := -K*(2:ℝ)^N
  have hc : c < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hK) (by positivity)
  let θ : ℝ≥0 := ⟨(2:ℝ)^c, (Real.rpow_pos_of_pos (by norm_num) _).le⟩
  refine ⟨θ, (show 0 < (2:ℝ)^c from Real.rpow_pos_of_pos (by norm_num) _), ?_, ?_⟩
  · change (2:ℝ)^c < 1
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hc
  have hdeg : (N:ℝ)<K*a := by dsimp [K]; rw [div_mul_cancel₀ _ ha.ne']; linarith
  have h := (entropy_rate_zero N δ N K hdeg).const_mul ((2:ℝ)^(-c))
  rw [mul_zero] at h
  apply h.congr
  intro d
  change _ = (d:ℝ)^N *((2:ℝ)^c)^(_-1)
  rw [← Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [show c*((largeDegreeMainTerm (N+1) d+δ)/(2:ℝ)^N-1) = -c + -K*(largeDegreeMainTerm (N+1) d+δ)
      by dsimp [c]; field_simp; ring, Real.rpow_add (by norm_num)]
  ring

end LpGowers.Discrete
