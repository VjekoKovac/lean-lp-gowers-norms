module

public import LpGowers.DiscreteProofs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Passage from the sampled critical inequality to the logarithmic
lower correction in Theorem 1.5(b). All logarithms in the target use base two. -/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace LpGowers.Discrete

/-- Pass to the limit in a family of discrete tests of masses A and B.
The inequality relative to n^(d+p) retains the additive logarithmic
correction when n tends to infinity. -/
theorem eventual_lower_of_sample {D : ℕ} {T A B : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b)) (hT : Tendsto T atTop (𝓝 (D : ℝ)))
    (hsample : ∀ᶠ n : ℕ in atTop, (n:ℝ)^D*A n ≤ ((n:ℝ)*B n)^(T n)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, logTwo a - (D:ℝ)*logTwo b - η ≤ (T n-D)*logTwo n := by
  have hlogA : Tendsto (fun n => logTwo (A n)) atTop (𝓝 (logTwo a)) :=
    (Real.continuousAt_logb ha.ne').tendsto.comp hA
  have hlogB : Tendsto (fun n => logTwo (B n)) atTop (𝓝 (logTwo b)) :=
    (Real.continuousAt_logb hb.ne').tendsto.comp hB
  have hlim := hlogA.sub (hT.mul hlogB)
  filter_upwards [hsample, eventually_ge_atTop 1, hA.eventually_const_lt ha, hB.eventually_const_lt hb,
    hlim.eventually_const_lt (show logTwo a-D*logTwo b-η < logTwo a-D*logTwo b by linarith)]
    with n hs hn ha' hb' hlow
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogs := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos (pow_pos hn' _) ha') hs
  rw [Real.logb_mul (pow_pos hn' _).ne' ha'.ne', Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos (mul_pos hn' hb'), Real.logb_mul hn'.ne' hb'.ne'] at hlogs
  change logTwo a-D*logTwo b-η < logTwo (A n)-T n*logTwo (B n) at hlow
  change _ ≤ (_-_)*Real.logb 2 n
  have h' : logTwo (A n)-T n*logTwo (B n) ≤ (T n-D)*Real.logb 2 n := by
    dsimp [logTwo]
    nlinarith only [hlogs]
  exact hlow.le.trans h'

/-- The positive coefficient permits the multiplicative (1+o(1)) error
used in the manuscript, for every degree and discrete outer exponent. -/
theorem correction_pos {d p : ℕ} (hd : 2 ≤ d) (hp : 1 ≤ p) : 0 < correction d p := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hD : 0 < (d:ℝ)+p := by positivity
  have hlog : logTwo p < logTwo ((d:ℝ)+p) :=
    (Real.strictMonoOn_logb (by norm_num : (1:ℝ)<2)) (show (p:ℝ) ∈ Set.Ioi 0 from by change 0 < (p:ℝ); linarith) hD (by linarith)
  by_cases h : 4 ≤ d+p
  · have hr : (4:ℝ) ≤ (d:ℝ)+p := by exact_mod_cast h
    have hz := Real.logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<4) hr
    have h4 : Real.logb 2 4 = 2 := by
      rw [show (4:ℝ)=2^(2:ℕ) by norm_num,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      norm_num
    rw [h4] at hz
    change 2 ≤ logTwo ((d:ℝ)+p) at hz
    unfold correction
    push_cast
    nlinarith only [mul_nonneg (show 0 ≤ (d:ℝ) by positivity) (sub_nonneg.mpr hz),
      mul_pos (by linarith : 0 < (p:ℝ)) (sub_pos.mpr hlog)]
  · obtain rfl : d=2 := by omega
    obtain rfl : p=1 := by omega
    have hlog3 := (Real.strictMonoOn_logb (by norm_num : (1:ℝ)<2))
      (show (16:ℝ)∈Set.Ioi 0 by norm_num) (show (27:ℝ)∈Set.Ioi 0 by norm_num) (by norm_num : (16:ℝ)<27)
    rw [show (16:ℝ) = 2^(4:ℕ) by norm_num, show (27:ℝ) = 3^(3:ℕ) by norm_num,
      Real.logb_pow,Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at hlog3
    norm_num [correction,logTwo] at hlog3 ⊢
    linarith

/-- Uniform eventual lower bounds with additive tolerance become the
single little-o function used in the quantified target. -/
theorem lower_correction_little_o {D C : ℝ} (hC : 0 < C) (T : ℕ → ℝ)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, -C-η ≤ (T n-D)*logTwo n) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, D-(1+e n)*C/logTwo n ≤ T n := by
  let e (n : ℕ) := max 0 (((D-T n)*logTwo n-C)/C)
  have he : Tendsto e atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [h (C*η/2) (by positivity)] with n hn
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (le_max_left .. : 0 ≤ e n)]
    refine max_lt hη ((div_lt_iff₀ hC).mpr ?_)
    nlinarith [mul_pos hC hη]
  refine ⟨e,he,?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < logTwo n := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have hx := (div_le_iff₀ hC).mp (le_max_right 0 (((D-T n)*logTwo n-C)/C))
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hlog]
  nlinarith only [hx]

end LpGowers.Discrete
