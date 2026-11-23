module

public import LpGowers.Discrete
import Mathlib.Tactic

/-! The constants for the absolute upper correction in Theorem 1.5(b).
The support loss is constant because the perturbation of the inverse exponent
is a fixed multiple of the reciprocal logarithm of the support size.
-/

@[expose] public section
noncomputable section
open scoped ENNReal NNReal
namespace LpGowers.Discrete

theorem additive_gap_parameters {δ : ℝ} (hd : 0<δ) (hd' : δ<1) :
    ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, 2≤n →
      let t := 3 - c/logTwo n
      let q := 4/t
      let D := (n:ℝ)^(1/(4/3:ℝ)-1/q)
      4/3 ≤ q ∧ q ≤ 3/2 ∧ D ≤ 2 ∧ (1-δ)*D ≤ 1 := by
  let c := min (1/3:ℝ) (4*Real.logb 2 (1-δ)⁻¹)
  have hx := sub_pos.mpr hd'
  have hinv : 1 < (1-δ)⁻¹ := (one_lt_inv₀ hx).mpr (by linarith)
  have hlog : 0 < Real.logb 2 (1-δ)⁻¹ := Real.logb_pos (by norm_num) hinv
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  refine ⟨c,hc,?_⟩
  intro n hn
  let l := logTwo n
  have hn' : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have h2l : 1 ≤ l := by
    change 1 ≤ Real.logb 2 n
    simpa using (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2) hn')
  have hl : 0<l := zero_lt_one.trans_le h2l
  have hc' : c ≤ 1/3 := min_le_left ..
  have hc0 := div_pos hc hl
  have hc1 : c/l ≤ 1/3 := (div_le_iff₀ hl).mpr (by nlinarith)
  let t := 3-c/l
  have ht0 : 0<t := by dsimp [t]; linarith
  have ht1 : t≤3 := by dsimp [t]; linarith
  have ht2 : 8/3≤t := by dsimp [t]; linarith
  have he : 1/(4/3:ℝ) - 1/(4/t) = c/(4*l) := by dsimp [t]; field_simp; ring
  have he' : (n:ℝ) ^ (c/(4*l)) = (2:ℝ) ^ (c/4) := by
    have hw : (n:ℝ) = (2:ℝ) ^ l := (Real.rpow_logb (by norm_num) (by norm_num) hn₀).symm
    rw [hw, ← Real.rpow_mul (by norm_num), show l*(c/(4*l)) = c/4 by field_simp]
  have hD : (2:ℝ)^(c/4) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show c/4≤1 by linarith) using 1; simp
  have hdD : (2:ℝ)^(c/4) ≤ (1-δ)⁻¹ := by
    rw [← Real.rpow_logb (b:=2) (by norm_num) (by norm_num) (inv_pos.mpr hx)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [show c≤4*Real.logb 2 (1-δ)⁻¹ from min_le_right ..]
  change 4/3 ≤ 4/t ∧ 4/t≤3/2 ∧ (n:ℝ) ^ _ ≤ 2 ∧ (1-δ)*(n:ℝ)^_ ≤ 1
  rw [he,he']
  refine ⟨(le_div_iff₀ ht0).mpr (by nlinarith), (div_le_iff₀ ht0).mpr (by nlinarith), hD, ?_⟩
  calc
    _ ≤ (1-δ)*(1-δ)⁻¹ := mul_le_mul_of_nonneg_left hdD hx.le
    _ = 1 := mul_inv_cancel₀ hx.ne'

/-- After normalizing the q-norm, the quadratic contribution from the tail
is absorbed by its q-mass. This remains uniform up through q=3/2. -/
theorem additive_gap_absorb {q a S T U : ℝ} (hq : 0<q) (hq' : q≤3/2)
    (ha : 0≤a) (hS : 0≤S) (hT : 0≤T) (_hU : 0≤U)
    (hm : a^q+S^q=1) (hsmall : T≤1/10000) (hcmp : T≤2*S)
    (henergy : U^4 ≤ a^4 + 11*T^2*(max a T)^2) : U ≤ 1 := by
  have ha' : a ≤ 1 := by
    rw [← Real.rpow_le_rpow_iff ha (by norm_num : 0≤(1:ℝ)) hq, Real.one_rpow]
    linarith [Real.rpow_nonneg hS q]
  have hS' : S ≤ 1 := by
    rw [← Real.rpow_le_rpow_iff hS (by norm_num : 0≤(1:ℝ)) hq, Real.one_rpow]
    linarith [Real.rpow_nonneg ha q]
  have hA : a^4 ≤ a^q := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' ha ha' hq.le (show q ≤ (4:ℝ) by linarith)
  have hZ : S^(3/2:ℝ) ≤ S^q := Real.rpow_le_rpow_of_exponent_ge' hS hS' hq.le hq'
  have hT1 : T^(1/2:ℝ) ≤ 1/100 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    exact ⟨by norm_num,by nlinarith⟩
  have hT3 : T^(3/2:ℝ) ≤ 4*S^(3/2:ℝ) := by
    have h2 : (2:ℝ)^(3/2:ℝ) ≤ 4 := by
      convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (by norm_num : (3/2:ℝ)≤2) using 1; norm_num
    apply (Real.rpow_le_rpow hT hcmp (by norm_num : (0:ℝ)≤3/2)).trans
    rw [Real.mul_rpow (by norm_num) hS]
    gcongr
  have hTs : T^2 ≤ 1/100 * (4*S^(3/2:ℝ)) := by
    calc
      _ = T^(1/2:ℝ)*T^(3/2:ℝ) := by rw [← Real.rpow_add_of_nonneg hT (by norm_num) (by norm_num)]; norm_num
      _ ≤ _ := mul_le_mul hT1 hT3 (Real.rpow_nonneg hT _) (by norm_num)
  have hh : 11*T^2 ≤ S^q := by nlinarith only [hTs,hZ,Real.rpow_nonneg hS (3/2)]
  have hm' : max a T ≤ 1 := max_le ha' (by linarith)
  have hu' : U^4 ≤ 1 := calc
    _ ≤ _ := henergy
    _ ≤ a^4 + 11*T^2*(1:ℝ)^2 := by gcongr
    _ ≤ 1 := by nlinarith only [hA,hh,hm]
  exact le_of_not_gt (fun hh => (not_lt_of_ge hu') (by simpa using pow_lt_pow_left₀ hh (by norm_num) (by decide : 4≠0)))

end LpGowers.Discrete
