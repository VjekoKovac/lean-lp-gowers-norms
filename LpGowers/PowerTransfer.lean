module

public import LpGowers.LebesgueNear
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Transferring closeness under powers of nonnegative functions

These estimates implement the final power change in the proof of Theorem
1.2(b), separately below and above the Lipschitz threshold. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace LpGowers

/-- Sublinear powers are Hölder of their precise order. -/
theorem edist_rpow_sublinear (x y : ℝ≥0) {γ : ℝ} (hg : 0 < γ) (hg1 : γ ≤ 1) :
    edist (x ^ γ) (y ^ γ) ≤ edist x y ^ γ := by
  have hordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      |a ^ γ - b ^ γ| ≤ |a - b| ^ γ := by
    have h := Real.rpow_add_le_add_rpow ha (sub_nonneg.mpr hab) hg.le hg1
    rw [add_sub_cancel] at h
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow ha hab hg.le)),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, neg_sub]
    linarith only [h]
  simp only [edist_dist, NNReal.dist_eq, NNReal.coe_rpow, ENNReal.ofReal_rpow_of_nonneg
    (abs_nonneg _) hg.le]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total (x : ℝ) (y : ℝ) with h | h
  · exact hordered _ _ x.2 h
  · rw [abs_sub_comm (x : ℝ) (y : ℝ), abs_sub_comm ((x : ℝ)^γ) ((y : ℝ)^γ)]
    exact hordered _ _ y.2 h

/-- Mean-value bound for a superlinear power, with the larger endpoint
controlling its derivative on the entire interval. -/
theorem edist_rpow_superlinear (x y : ℝ≥0) {γ : ℝ} (hg : 1 < γ) :
    edist (x ^ γ) (y ^ γ) ≤
      ENNReal.ofReal γ * (max (x : ℝ≥0∞) (y : ℝ≥0∞)) ^ (γ - 1) * edist x y := by
  have hordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      |a ^ γ - b ^ γ| ≤ γ * (max a b) ^ (γ - 1) * |a - b| := by
    rcases hab.eq_or_lt with rfl | hab
    · simp
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (fun v : ℝ => v^γ)
      (fun v => γ * v ^ (γ-1)) hab
      (continuousOn_of_forall_continuousAt (fun v _ =>
        (Real.hasDerivAt_rpow_const (.inr hg.le) (x := v)).continuousAt))
      (fun v _ => Real.hasDerivAt_rpow_const (.inr hg.le))
    have hd : γ * c ^ (γ-1) ≤ γ * b ^ (γ-1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha.trans hc.1.le) hc.2.le
        (sub_nonneg.mpr hg.le)) (zero_lt_one.trans hg).le
    have hm := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hab.le)
    rw [(eq_div_iff (sub_pos.mpr hab).ne').mp he] at hm
    rw [max_eq_right hab.le,
      abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow ha hab.le (zero_lt_one.trans hg).le)),
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub, neg_sub]
    exact hm
  have hreal : |(x : ℝ)^γ - (y : ℝ)^γ| ≤
      γ * max (x : ℝ) (y : ℝ) ^ (γ-1) * |(x : ℝ)-y| := by
    rcases le_total (x : ℝ) (y : ℝ) with h | h
    · exact hordered _ _ x.2 h
    · rw [max_comm (x : ℝ) (y : ℝ), abs_sub_comm (x : ℝ) (y : ℝ),
        abs_sub_comm ((x : ℝ)^γ) ((y : ℝ)^γ)]
      exact hordered _ _ y.2 h
  have hmax : (max (x : ℝ≥0∞) (y : ℝ≥0∞)) = ENNReal.ofReal (max (x : ℝ) (y : ℝ)) := by
    simp
  simp only [edist_dist, NNReal.dist_eq, NNReal.coe_rpow, hmax]
  have hm : 0 ≤ max (x : ℝ) (y : ℝ) := le_max_of_le_left x.2
  rw [ENNReal.ofReal_rpow_of_nonneg hm (sub_nonneg.mpr hg.le),
    ← ENNReal.ofReal_mul (zero_lt_one.trans hg).le,
    ← ENNReal.ofReal_mul (mul_nonneg (zero_lt_one.trans hg).le (Real.rpow_nonneg hm _))]
  exact ENNReal.ofReal_le_ofReal hreal

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- Power continuity in the sublinear case for the exact two Lebesgue
exponents, with no integrability or normalization hypothesis. -/
theorem lpDist_rpow_sublinear {r γ : ℝ} (hr : 0 < r) (hg : 0 < γ) (hg1 : γ ≤ 1)
    (f g : X → ℝ≥0) :
    lpDist ν (r/γ) (fun x => f x ^ γ) (fun x => g x ^ γ) ≤ lpDist ν r f g ^ γ := by
  have hr' := div_pos hr hg
  have he : γ * (r/γ) = r := by field_simp
  have hpoint (x) := ENNReal.rpow_le_rpow (edist_rpow_sublinear (f x) (g x) hg hg1) hr'.le
  simp only [← ENNReal.rpow_mul, he] at hpoint
  have h := ENNReal.rpow_le_rpow (lintegral_mono (μ := ν) hpoint) (one_div_nonneg.mpr hr'.le)
  have he' : 1 / (r/γ) = (1/r)*γ := by field_simp
  simpa only [lpDist, lp, ← ENNReal.rpow_mul, he'] using h

/-- In the superlinear case the maximum of two unit-moment inputs has moment
at most two. Hölder applied to the pointwise mean-value bound gives this
uniform Lipschitz estimate on the unit sphere. -/
theorem lpDist_rpow_superlinear {r γ : ℝ} (hr : 0 < r) (hg : 1 < γ)
    {f g : X → ℝ≥0} (hf : AEMeasurable f ν) (hgM : AEMeasurable g ν)
    (hf1 : (∫⁻ x, (f x : ℝ≥0∞)^r ∂ν) = 1)
    (hg1 : (∫⁻ x, (g x : ℝ≥0∞)^r ∂ν) = 1) :
    lpDist ν (r/γ) (fun x => f x ^ γ) (fun x => g x ^ γ) ≤
      (ENNReal.ofReal γ * (2 : ℝ≥0∞) ^ ((γ-1)/r)) * lpDist ν r f g := by
  let C := ENNReal.ofReal γ
  let M := fun x => max (f x : ℝ≥0∞) (g x : ℝ≥0∞)
  let D := fun x => edist (f x) (g x)
  let a := (γ-1)/γ
  let b := 1/γ
  let s := r/γ
  have hgp := zero_lt_one.trans hg
  have hs : 0 < s := div_pos hr hgp
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hg.le) hgp.le
  have hb : 0 ≤ b := one_div_nonneg.mpr hgp.le
  have hab : a+b = 1 := by dsimp [a,b]; field_simp; ring
  have has : (γ-1)*s = r*a := by dsimp [a,s]; ring
  have hbs : r*b = s := by dsimp [b,s]; ring
  have hM : AEMeasurable M ν := hf.coe_nnreal_ennreal.max hgM.coe_nnreal_ennreal
  have hD : AEMeasurable D ν := hf.edist hgM
  have hMI : (∫⁻ x, M x ^ r ∂ν) ≤ 2 := by
    calc
      _ ≤ ∫⁻ x, (f x : ℝ≥0∞) ^ r + (g x : ℝ≥0∞) ^ r ∂ν := by
        apply lintegral_mono
        intro x
        exact (ENNReal.max_rpow hr.le).le.trans (max_le (le_self_add) (le_add_self))
      _ = _ := by rw [lintegral_add_left' (hf.coe_nnreal_ennreal.pow_const r), hf1, hg1]; norm_num
  have hpoint (x) :
      edist (f x ^ γ) (g x ^ γ) ^ s ≤ C ^ s * ((M x ^ r) ^ a * (D x ^ r) ^ b) := by
    have h := ENNReal.rpow_le_rpow (edist_rpow_superlinear (f x) (g x) hg) hs.le
    simpa only [M,D,C,ENNReal.mul_rpow_of_nonneg _ _ hs.le, ← ENNReal.rpow_mul, has, hbs,
      mul_assoc] using h
  have hw := ENNReal.lintegral_mul_norm_pow_le (hM.pow_const r) (hD.pow_const r) ha hb hab
  have hI : (∫⁻ x, edist (f x ^ γ) (g x ^ γ) ^ s ∂ν) ≤
      C ^ s * (2 ^ a * (∫⁻ x, D x ^ r ∂ν) ^ b) := by
    calc
      _ ≤ _ := lintegral_mono hpoint
      _ = _ := lintegral_const_mul'' _ (((hM.pow_const r).pow_const a).mul ((hD.pow_const r).pow_const b))
      _ ≤ _ := mul_le_mul le_rfl (hw.trans (mul_le_mul (ENNReal.rpow_le_rpow hMI ha) le_rfl
        zero_le zero_le)) zero_le zero_le
  have hpow := ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hs.le)
  have he1 : a * (1/s) = (γ-1)/r := by dsimp [a,s]; field_simp
  have he2 : b * (1/s) = 1/r := by dsimp [b,s]; field_simp
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hs.le), ← ENNReal.rpow_mul,
    he1, he2, mul_one_div_cancel hs.ne', ENNReal.rpow_one] at hpow
  simpa only [lpDist,lp,s,C,D,mul_assoc] using hpow

/-- The tolerance in the power-change step is uniform over all measure spaces
and unit-moment inputs. -/
theorem power_transfer_tolerance.{u} {r γ η : ℝ} (hr : 0 < r) (hg : 0 < γ) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (Y : Type u) [MeasurableSpace Y] (ν : Measure Y)
      (f g : Y → ℝ≥0), AEMeasurable f ν → AEMeasurable g ν →
      (∫⁻ x, (f x : ℝ≥0∞)^r ∂ν) = 1 → (∫⁻ x, (g x : ℝ≥0∞)^r ∂ν) = 1 →
      lpDist ν r f g ≤ ENNReal.ofReal τ →
      lpDist ν (r/γ) (fun x => f x ^ γ) (fun x => g x ^ γ) ≤ ENNReal.ofReal η := by
  by_cases h1 : γ ≤ 1
  · refine ⟨η ^ (1/γ), Real.rpow_pos_of_pos hη _, ?_⟩
    intro Y _ ν f g _ _ _ _ h
    refine (lpDist_rpow_sublinear ν hr hg h1 f g).trans ((ENNReal.rpow_le_rpow h hg.le).trans_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_pos_of_pos hη _).le hg.le,
      ← Real.rpow_mul hη.le, one_div_mul_cancel hg.ne', Real.rpow_one]
  · have h1' := lt_of_not_ge h1
    let C := γ * (2 : ℝ) ^ ((γ-1)/r)
    have hC : 0 < C := mul_pos hg (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨η/C, div_pos hη hC, ?_⟩
    intro Y _ ν f g hf hgM hf1 hg1 h
    refine (lpDist_rpow_superlinear ν hr h1' hf hgM hf1 hg1).trans
      ((mul_le_mul le_rfl h zero_le zero_le).trans_eq ?_)
    have hc : ENNReal.ofReal C = ENNReal.ofReal γ * (2 : ℝ≥0∞)^((γ-1)/r) := by
      rw [ENNReal.ofReal_mul hg.le, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (div_nonneg (sub_nonneg.mpr h1'.le) hr.le)]
      norm_num
    rw [← hc, ← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ η hC.ne']

end LpGowers
