module

public import LpGowers.DiscreteProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # The binary scalar inequality from Section 8

The monotonicity argument is adapted from the proof of Lemma 12 in Crmarić,
Kovač and Shiraki, *Inequalities in Fourier analysis on binary cubes*,
arXiv:2507.01359. We use the exponential coordinate rather than the hyperbolic
cosine and bound the derivative using the tangent-line inequality for log.
-/

@[expose] public section
noncomputable section
namespace LpGowers.Discrete
open Real

/-- Binary entropy dominates its quadratic lower bound, expressed in odds z. -/
private theorem binary_entropy_lower (z : ℝ) (hz : 0 < z) (hz' : z ≤ 1) :
    4 * z * log 2 ≤ (1+z)^2 * (log (1+z) - z*log z/(1+z)) := by
  let F (x : ℝ) := (1+x)^2 / x * log (1+x) - (1+x) * log x
  have hF (x : ℝ) (hx : 0 < x) :
      HasDerivAt F ((1-1/x^2)*log (1+x) - log x) x := by
    have hall := (((((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).pow 2).div
      (hasDerivAt_id x) hx.ne').mul (((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).log (by linarith : 1+x ≠ 0))).sub
      (((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).mul (Real.hasDerivAt_log hx.ne'))
    convert hall using 1
    · rfl
    dsimp
    field_simp [show 1+x ≠ 0 by linarith]
    ring
  have hanti : AntitoneOn F (Set.Icc z 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hF x (hz.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hF x (hz.trans_le (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    intro x hx
    obtain ⟨hx0,hx1⟩ := Set.mem_Ioo.mp (show x ∈ Set.Ioo z 1 by simpa using hx)
    have hx := hz.trans hx0
    rw [(hF x hx).deriv]
    have hlog : x/(1+x) ≤ log (1+x) := by
      convert one_sub_inv_le_log_of_pos (show 0 < 1+x by linarith) using 1
      field_simp
      ring
    have hcoeff : 0 ≤ 1/x^2-1 := by
      rw [le_sub_iff_add_le, zero_add, le_div_iff₀ (by positivity)]
      nlinarith
    have hlogx := Real.one_sub_inv_le_log_of_pos hx
    have h := mul_le_mul_of_nonneg_left hlog hcoeff
    have heq : (1/x^2-1)*(x/(1+x)) = x⁻¹-1 := by
      field_simp
      ring
    rw [heq] at h
    linarith
  have hh := hanti ⟨le_rfl, hz'⟩ ⟨hz', le_rfl⟩ hz'
  dsimp [F] at hh
  norm_num at hh
  field_simp at hh ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 1+z by linarith)]



private def binaryPhi (a s : ℝ) := exp (s * log (1+exp (a/s))) - exp (s*log 2 + a/2)

private theorem binaryPhi_deriv (a s : ℝ) (hs : 0 < s) :
    HasDerivAt (binaryPhi a)
      (exp (s*log (1+exp (a/s))) * (log (1+exp (a/s)) - exp (a/s)*log (exp (a/s))/(1+exp (a/s))) -
        exp (s*log 2 + a/2)*log 2) s := by
  have ha := ((hasDerivAt_const s a).div (hasDerivAt_id s) hs.ne').exp
  have hlog := ((hasDerivAt_const s (1:ℝ)).add ha).log (by dsimp; positivity)
  have H := ((hasDerivAt_id s).mul hlog).exp.sub (((hasDerivAt_id s).mul_const (log 2)).add_const (a/2)).exp
  convert H using 1
  · rfl
  dsimp
  simp only [log_exp]
  field_simp
  ring

/-- Monotonicity in the exponent from the proof of CKS Lemma 12. Writing
a=-2u converts this into monotonicity of 2^s (cosh(u/s)^s-1). -/
private theorem binaryPhi_mono (a : ℝ) (ha : a ≤ 0) :
    MonotoneOn (binaryPhi a) (Set.Ici 2) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro s hs
    exact (binaryPhi_deriv a s (lt_of_lt_of_le (by norm_num) hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact (binaryPhi_deriv a s (lt_of_lt_of_le (by norm_num) (interior_subset hs))).differentiableAt.differentiableWithinAt
  intro s hsi
  have hs2 : 2 < s := by simpa using hsi
  have hs : 0 < s := by linarith
  rw [(binaryPhi_deriv a s hs).deriv, sub_nonneg]
  let z := exp (a/s)
  let r := exp (a/s/2)
  have hz : 0 < z := exp_pos _
  have hz1 : z ≤ 1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg ha hs.le)
  have hr : 0 < r := exp_pos _
  have hrz : r^2 = z := by dsimp [r,z]; rw [sq, ← exp_add]; congr 1; ring
  have hB : 0 < 1+z := by positivity
  have hrB : 2*r / (1+z) ≤ 1 := by
    apply (div_le_iff₀ hB).mpr
    nlinarith [sq_nonneg (1-r)]
  have hrat := Real.rpow_le_rpow_of_exponent_ge (show 0 < 2*r/(1+z) by positivity) hrB hs2.le
  rw [Real.rpow_two, Real.div_rpow (by positivity) hB.le] at hrat
  have hi := binary_entropy_lower z hz hz1
  have hfrac : (2*r/(1+z))^2*log 2 ≤ log (1+z) - z*log z/(1+z) := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [mul_pow, hrz, mul_comm (log _ - _)]
    norm_num only [Nat.reducePow, one_div] at *
    linarith
  have hratio := (mul_le_mul_of_nonneg_right hrat (Real.log_nonneg (by norm_num))).trans hfrac
  rw [div_mul_eq_mul_div, div_le_iff₀ (Real.rpow_pos_of_pos hB _)] at hratio
  have he1 : exp (s*log (1+z)) = (1+z)^s := by rw [Real.rpow_def_of_pos hB]; congr 1; ring
  have he2 : exp (s*log 2+a/2) = (2*r)^s := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by norm_num) hr.ne']
    dsimp [r]
    rw [log_exp]
    congr 1
    field_simp
  change exp (s*log 2+a/2)*log 2 ≤ exp (s*log (1+z)) * (log (1+z)-z*log z/(1+z))
  rw [he1,he2]
  simpa [mul_comm] using hratio



private theorem binaryPhi_log (v t s : ℝ) (hv : 0 < v) :
    binaryPhi (t*log v) s =
      (1+v^(t/s))^s - 2^s * v^(t/2) := by
  unfold binaryPhi
  have heq (s : ℝ) : exp (t*log v/s) = v^(t/s) := by
    rw [Real.rpow_def_of_pos hv]
    congr 1
    ring
  rw [heq, Real.exp_add, heq, Real.rpow_def_of_pos (show 0 < 1+v^(t/s) by positivity),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  simp only [mul_comm s]

private theorem binary_scalar_normalized (p t v : ℝ) (hp : 2 ≤ p) (ht : p ≤ t)
    (hv : 0 < v) (hv' : v ≤ 1) :
    (1+v^(t/p))^p + (2^t-2^p)*v^(t/2) ≤ (1+v)^t := by
  have ht' : 0 < t := by linarith
  have hh := binaryPhi_mono (t*log v)
    (mul_nonpos_of_nonneg_of_nonpos ht'.le (Real.log_nonpos hv.le hv')) hp (hp.trans ht) ht
  rw [binaryPhi_log v t p hv, binaryPhi_log v t t hv, div_self ht'.ne', Real.rpow_one] at hh
  linarith

/-- Section 8, the sharp scalar estimate for all real t ≥ p ≥ 2 and
nonnegative inputs. Taking t=log₂(2^p+2d) gives the coefficient 2d. -/
theorem binary_scalar_inequality (p t : ℝ) (hp : 2 ≤ p) (ht : p ≤ t)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x^(t/p)+y^(t/p))^p + (2^t-2^p)*(x*y)^(t/2) ≤ (x+y)^t := by
  have hpp : 0 < p := by linarith
  have htt : 0 < t := by linarith
  have htp : 0 < t/p := div_pos htt hpp
  wlog hyx : y ≤ x generalizing x y
  · simpa only [add_comm (y^(t/p)), mul_comm y x, add_comm y x] using
      this y x hy hx (le_of_not_ge hyx)
  rcases hy.eq_or_lt with rfl | hy'
  · simp [Real.zero_rpow htp.ne', Real.zero_rpow (by linarith : t/2 ≠ 0),
      ← Real.rpow_mul hx, div_mul_cancel₀ _ hpp.ne']
  have hx' : 0 < x := hy'.trans_le hyx
  let v := y/x
  have hv : 0 < v := div_pos hy' hx'
  have hv' : v ≤ 1 := (div_le_one hx').mpr hyx
  have hyv : y = x*v := by dsimp [v]; field_simp
  have hnorm := mul_le_mul_of_nonneg_left (binary_scalar_normalized p t v hp ht hv hv') (Real.rpow_nonneg hx t)
  rw [hyv]
  have he (a b : ℝ) : (x^a)^b = x^(a*b) := (Real.rpow_mul hx _ _).symm
  have h1 : (x^(t/p) + (x*v)^(t/p))^p = x^t*(1+v^(t/p))^p := by
    rw [Real.mul_rpow hx hv.le, ← mul_one_add, Real.mul_rpow (by positivity) (by positivity),
      he, div_mul_cancel₀ _ hpp.ne']
  have h2 : (x*(x*v))^(t/2) = x^t*v^(t/2) := by
    rw [← mul_assoc, ← sq, Real.mul_rpow (by positivity) hv.le, ← Real.rpow_natCast_mul hx]
    rw [show (↑(2:ℕ):ℝ)*(t/2) = t by push_cast; ring]
  rw [h1,h2,← mul_one_add, Real.mul_rpow hx (by positivity)]
  linarith



private theorem binary_scalar_one (t : ℝ) (ht : 2 ≤ t) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^t + y^t + (2^t-2)*(x*y)^(t/2) ≤ (x+y)^t := by
  have H := binary_scalar_inequality 2 t le_rfl ht x y hx hy
  rw [Real.rpow_two, add_sq, Real.mul_rpow hx hy, ← Real.rpow_mul_natCast hx,
    ← Real.rpow_mul_natCast hy, Real.rpow_two] at H
  norm_num1 at H
  rw [show t/2*2 = t by ring] at H
  rw [Real.mul_rpow hx hy]
  linarith

/-- The exact scalar estimate used in Theorem 1.5(a), including p=1. -/
theorem binary_scalar_sharp (d k : ℕ) (hd : 1 ≤ d) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let t := logTwo ((2:ℝ)^(k+1) + 2*d)
    (x^(t/(k+1:ℕ))+y^(t/(k+1:ℕ)))^(k+1) + (2*d : ℝ)*(x*y)^(t/2) ≤ (x+y)^t := by
  let t := logTwo ((2:ℝ)^(k+1) + 2*d)
  have hxpos : 0 < (2:ℝ)^(k+1)+2*d := by positivity
  have h2 : (2:ℝ)^t = (2:ℝ)^(k+1)+2*d := Real.rpow_logb (by norm_num) (by norm_num) hxpos
  have ht : (k+1:ℕ) ≤ t := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
    rw [h2, Real.rpow_natCast]
    exact le_add_of_nonneg_right (by positivity)
  change _ + _ * (x*y)^(t/2) ≤ (x+y)^t
  cases k with
  | zero =>
    have ht2 : 2 ≤ t := by
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mp
      rw [h2, Real.rpow_two]
      have hh : 1 ≤ (d:ℝ) := by exact_mod_cast hd
      norm_num
      linarith
    have H := binary_scalar_one t ht2 x y hx hy
    rw [h2] at H
    simpa [t] using H
  | succ k =>
    have hp : 2 ≤ ((k+1+1:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ k+1+1 by omega)
    have H := binary_scalar_inequality _ t hp ht x y hx hy
    simp only [h2, Real.rpow_natCast, add_sub_cancel_left] at H
    simpa [t] using H

end LpGowers.Discrete
