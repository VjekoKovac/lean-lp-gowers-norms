module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! A homogeneous strict Taylor estimate for the signed power on the real line.
The two terms are designed to give a norm estimate after Hölder's inequality. -/
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false
namespace LpGowers

def signedPower (g x : ℝ) : ℝ := x * |x| ^ (g-1)

lemma signedPower_nonneg_value {g x : ℝ} (hg : 1 ≤ g) (hx : 0 ≤ x) :
    signedPower g x = x^g := by
  unfold signedPower
  rw [abs_of_nonneg hx]
  by_cases h : x = 0
  · simp [h,Real.zero_rpow (by linarith : g ≠ 0)]
  calc
    x*x^(g-1) = x^(1:ℝ)*x^(g-1) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add (lt_of_le_of_ne hx (Ne.symm h))]; congr 1; ring

theorem hasDerivAt_signedPower {g : ℝ} (hg : 1 ≤ g) (x : ℝ) :
    HasDerivAt (signedPower g) (g * |x|^(g-1)) x := by
  rcases hg.eq_or_lt with rfl | hg
  · have he : signedPower 1 = id := by funext y; simp [signedPower]
    rw [he]; simpa using hasDerivAt_id x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := ((Real.hasDerivAt_rpow_const (x := -x) (p := g) (Or.inr hg.le)).comp x
      (hasDerivAt_neg x)).neg
    rw [abs_of_neg hx]
    convert h.congr_of_eventuallyEq (f₁ := signedPower g) ?_ using 1 <;> try ring
    filter_upwards [gt_mem_nhds hx] with y hy
    have := signedPower_nonneg_value hg.le (neg_nonneg.mpr hy.le)
    simpa [signedPower,abs_of_neg hy] using congrArg Neg.neg this
  · have hcont : Continuous (fun t : ℝ => |t| ^ (g-1)) :=
      continuous_abs.rpow_const (fun _ => Or.inr (by linarith))
    rw [hasDerivAt_iff_tendsto_slope]
    have hz : (0:ℝ)^(g-1)=0 := Real.zero_rpow (by linarith)
    have h := (hcont.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
    apply Filter.Tendsto.congr' _ (by simpa [hz] using h : Tendsto
      (fun t : ℝ => |t|^(g-1)) (𝓝[≠] 0) (𝓝 (g*|0|^(g-1))))
    filter_upwards [self_mem_nhdsWithin] with y (hy : y≠0)
    simp [slope_def_field,signedPower,hy]
  · rw [abs_of_pos hx]
    apply (Real.hasDerivAt_rpow_const (x := x) (p := g) (Or.inr hg.le)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    exact signedPower_nonneg_value hg.le hy.le

/-- The variation of the absolute power at arbitrary amplitudes is bounded by a
small multiple of the base amplitude and a controlled power of the displacement. -/
private lemma absPower_difference {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      abs (|a|^m - |b|^m) ≤ ε * |b|^m + C * |a-b|^m := by
  have hc : ContinuousAt (fun t : ℝ => t^m) 1 :=
    (continuous_id.rpow_const (fun _ => Or.inr hm.le)).continuousAt
  obtain ⟨d,hd,hD⟩ := Metric.continuousAt_iff.mp hc ε hε
  let K := 1 / d
  have hK : 0 < K := one_div_pos.mpr hd
  refine ⟨(K+1)^m+K^m, by positivity, ?_⟩
  intro a b
  by_cases h : |a-b| < d * |b|
  · have hb : 0 < |b| := pos_of_mul_pos_right ((abs_nonneg _).trans_lt h) hd.le
    have hr : dist (|a|/|b|) 1 < d := by
      rw [Real.dist_eq,div_sub_one hb.ne',abs_div,abs_abs,div_lt_iff₀ hb]
      exact (abs_abs_sub_abs_le_abs_sub a b).trans_lt h
    have hh := hD hr
    simp only [Real.dist_eq, Real.one_rpow] at hh
    have hb' := Real.rpow_pos_of_pos hb m
    rw [Real.div_rpow (abs_nonneg _) hb.le,div_sub_one hb'.ne',abs_div,
      abs_of_pos hb',div_lt_iff₀ hb'] at hh
    exact hh.le.trans (le_add_of_nonneg_right (by positivity))
  · have h1 : |b| ≤ K*|a-b| := by
      dsimp [K]
      rw [one_div_mul_eq_div,le_div_iff₀ hd]
      linarith only [not_lt.mp h]
    have h2 : |a| ≤ (K+1)*|a-b| := by
      have he := abs_add_le (a-b) b
      rw [sub_add_cancel] at he
      linarith only [he,h1]
    have P := Real.rpow_le_rpow (abs_nonneg _) h1 hm.le
    have Q := Real.rpow_le_rpow (abs_nonneg _) h2 hm.le
    rw [Real.mul_rpow hK.le (abs_nonneg _)] at P
    rw [Real.mul_rpow (by positivity) (abs_nonneg _)] at Q
    have he := abs_sub (|a|^m) (|b|^m)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at he
    nlinarith only [P,Q,he,mul_nonneg hε.le (Real.rpow_nonneg (abs_nonneg b) m)]

/-- The scalar estimate which yields strict differentiability between
the sharp input and output Lebesgue exponents. -/
theorem signedPower_strict_remainder {g ε : ℝ} (hg : 1 < g) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z : ℝ,
      |signedPower g x - signedPower g y - g*|z|^(g-1)*(x-y)| ≤
        (ε*|z|^(g-1) + C*(|x-z|+|y-z|)^(g-1))*|x-y| := by
  have hg' : 0 < g := zero_lt_one.trans hg
  obtain ⟨K,hK,H⟩ := absPower_difference (sub_pos.mpr hg) (div_pos hε hg')
  refine ⟨g*K,mul_nonneg hg'.le hK,?_⟩
  intro x y z
  let f := fun t => signedPower g t - g*|z|^(g-1)*t
  let f' := fun t => g*|t|^(g-1)-g*|z|^(g-1)
  have hf (t) : HasDerivAt f (f' t) t := by
    simpa [f,f', Pi.sub_def] using (hasDerivAt_signedPower hg.le t).sub ((hasDerivAt_id t).const_mul (g*|z|^(g-1)))
  have hseg (u v : ℝ) (huv : u < v) : |f v - f u| ≤
      (ε*|z|^(g-1)+g*K*(|u-z|+|v-z|)^(g-1))*|v-u| := by
    obtain ⟨t,ht,hm⟩ := exists_hasDerivAt_eq_slope f f' huv
      (continuous_iff_continuousAt.2 (fun t => (hf t).continuousAt)).continuousOn (fun t _ => hf t)
    have ht' : |t-z| ≤ |u-z| + |v-z| := by
      rw [abs_le]
      constructor <;> linarith [ht.1,ht.2,le_abs_self (u-z),neg_abs_le (u-z),
        le_abs_self (v-z),neg_abs_le (v-z),abs_nonneg (u-z),abs_nonneg (v-z)]
    have hd := (H t z).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) ht' (sub_nonneg.mpr hg.le)) hK) _)
    have hh : |f' t| ≤ ε*|z|^(g-1)+g*K*(|u-z|+|v-z|)^(g-1) := by
      dsimp [f']; rw [← mul_sub,abs_mul,abs_of_pos hg']
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left hd hg'.le
        _ = _ := by field_simp
    rw [eq_div_iff (sub_ne_zero.mpr huv.ne')] at hm
    rw [← hm,abs_mul]
    exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)
  have eq (a b : ℝ) : signedPower g a - signedPower g b - g*|z|^(g-1)*(a-b) = f a-f b := by
    dsimp [f]; ring
  rw [eq]
  rcases lt_trichotomy x y with h|rfl|h
  · simpa only [abs_sub_comm (f y) (f x),abs_sub_comm y x] using hseg x y h
  · simp
  · simpa only [add_comm |y-z| |x-z|] using hseg y x h

end LpGowers
