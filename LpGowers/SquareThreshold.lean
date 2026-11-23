module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! Numerical end of the square-leakage argument in §6. All constants and
the square-root bound are established with kernel-checked real arithmetic. -/

@[expose] public section
noncomputable section
open scoped ENNReal NNReal
namespace LpGowers

private theorem squareThreshold_real (m a b F : ℝ) (hm : 0 ≤ m) (hF : 0 ≤ F)
    (ha : 1 - 1/10^12 ≤ a) (hb : 1 - 1/10^12 ≤ b) (ha' : a ≤ 1 + 1/10^12)
    (hab : a*b ≤ m*m + 3*(1/10^12)) (hma : m ≤ a) (hF' : F ≤ 1+1/10^12) :
    0 < m ∧ 2*(1/10^12) +
    (max (F^2+(m*max (1-m) 0+2*(1/10^12))-m) 0)^(1/2:ℝ)*F*2 < m^2/100 := by
  have ha0 : (0:ℝ) ≤ 1-1/10^12 := by norm_num
  have hprod := mul_le_mul ha hb ha0 (ha0.trans ha)
  have hmlo : 1-1/10^8 ≤ m := by
    by_contra! h
    have he := mul_self_lt_mul_self hm h
    nlinarith only [he, hprod, hab]
  have hsize : m ≤ 2 := by linarith
  have hs : max (1-m) 0 ≤ 1/10^8 := max_le (by linarith) (by norm_num)
  have hmul := mul_le_mul hsize hs (le_max_right _ _) (by norm_num)
  have hFs := mul_self_le_mul_self hF hF'
  let R := max (F^2+(m*max (1-m) 0+2*(1/10^12))-m) 0
  have hR : R ≤ 1/10^6 := max_le (by nlinarith only [hFs, hmul,hmlo]) (by norm_num)
  have hsqrt : R^(1/2:ℝ) ≤ 1/1000 := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · convert hR using 1
      norm_num
  have hF2 : F ≤ 2 := by linarith
  have hterm := mul_le_mul hsqrt hF2 hF (by norm_num)
  have hm2 := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1-1/10^8) hmlo
  exact ⟨by linarith, by change 2*(1/10^12) + R^(1/2:ℝ)*F*2 < _; nlinarith only [hm2,hterm]⟩

/-- For tolerance 10⁻¹² the square-leakage bound is strictly below the
one-percent threshold for the additive small-leakage criterion. -/
theorem square_leakage_threshold {m a b F L : ℝ≥0∞}
    (ha : 1 - 1/10^12 ≤ a) (hb : 1 - 1/10^12 ≤ b)
    (ha' : a ≤ 1+1/10^12) (hb' : b ≤ 1+1/10^12)
    (hab : a*b ≤ m*m+3*(1/10^12)) (hma : m ≤ a) (hF : F ≤ 1+1/10^12)
    (hL : L ≤ 2*(1/10^12) +
      ((F^2 + (m*(1-m)+2*(1/10^12)) - m)^(1/2:ℝ))*F*2) :
    0 < m ∧ m ≠ ⊤ ∧ L < m^2/100 := by
  let t : ℝ≥0 := 1/10^12
  have he : ((t : ℝ≥0) : ℝ≥0∞) = 1/10^12 := by simp [t]
  have ht : (1:ℝ≥0∞) + 1/10^12 ≠ ⊤ := by rw [← he]; finiteness
  lift a to ℝ≥0 using (ha'.trans_lt ht.lt_top).ne
  lift b to ℝ≥0 using (hb'.trans_lt ht.lt_top).ne
  lift F to ℝ≥0 using (hF.trans_lt ht.lt_top).ne
  lift m to ℝ≥0 using (hma.trans_lt ENNReal.coe_lt_top).ne
  rw [← he] at ha hb ha' hab hF
  norm_cast at ha hb ha' hab hma hF
  have htR : (t : ℝ) = 1/10^12 := by simp [t]
  have ha₁ := (show (((1:ℝ≥0)-t : ℝ≥0):ℝ) ≤ a by exact_mod_cast ha)
  have hb₁ := (show (((1:ℝ≥0)-t : ℝ≥0):ℝ) ≤ b by exact_mod_cast hb)
  rw [NNReal.coe_sub_def, NNReal.coe_one, htR, max_eq_left (by norm_num)] at ha₁ hb₁
  have hab' := (show ((a*b:ℝ≥0):ℝ) ≤ (m*m+3*t:ℝ≥0) by exact_mod_cast hab)
  have ha₂ := (show (a:ℝ) ≤ (1+t:ℝ≥0) by exact_mod_cast ha')
  have hF₂ := (show (F:ℝ) ≤ (1+t:ℝ≥0) by exact_mod_cast hF)
  push_cast at hab' ha₂ hF₂
  rw [htR] at hab' ha₂ hF₂
  have H := squareThreshold_real m a b F m.coe_nonneg F.coe_nonneg ha₁ hb₁ ha₂ hab'
    (by exact_mod_cast hma) hF₂
  refine ⟨?_, ENNReal.coe_ne_top, hL.trans_lt ?_⟩
  · exact_mod_cast H.1
  · rw [← he]
    suffices h : 2*t + ((F^2+(m*(1-m)+2*t)-m)^(1/2:ℝ))*F*2 < m^2/100 by
      simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_pow,
        ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0:ℝ) ≤ 1/2), ENNReal.coe_one,
        ENNReal.coe_ofNat, ENNReal.coe_div (by norm_num : (100:ℝ≥0)≠0)] using
        (ENNReal.coe_lt_coe.mpr h)
    apply NNReal.coe_lt_coe.mp
    push_cast
    simp only [NNReal.coe_sub_def, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_one, NNReal.coe_ofNat, htR]
    exact H.2

end LpGowers
