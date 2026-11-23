module

public import LpGowers.SymmetricLowering
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Reduction of near-extremisers to the ordinary Gowers inequality

Section 3 works with the input normalised to a unit critical moment. The
two interpolation arguments below preserve the power of the ordinary Gowers
quantity; it is strictly positive on either side of `p = 1`. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace LpGowers

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]

/-- Two successive applications of weighted Hölder, first to the base point
of a cube and then to its increments. This is equation (2.5) at positive
finite exponents, including quasi-norms. -/
theorem gowers_geometric_le (d : ℕ) {f g : G → ℝ≥0} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) {a b p s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hp : 0 < p) (hs : 0 < s) (ht : 0 < t)
    (hrel : 1 / p = a / s + b / t) :
    gowers μ d p (fun x => f x ^ a * g x ^ b) ≤ gowers μ d s f ^ a * gowers μ d t g ^ b := by
  let A := a * p / s
  let B := b * p / t
  let F := autocorrelation μ d f
  let H := autocorrelation μ d g
  let R := autocorrelation μ d (fun x => f x ^ a * g x ^ b)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg ha hp.le) hs.le
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hb hp.le) ht.le
  have hAB : A + B = 1 := by
    calc
      _ = p * (a / s + b / t) := by dsimp [A,B]; ring
      _ = 1 := by rw [← hrel]; field_simp
  have hAs : s * A = a * p := by dsimp [A]; field_simp
  have hBt : t * B = b * p := by dsimp [B]; field_simp
  have hpw (x) : R x ^ p ≤ (F x ^ s) ^ A * (H x ^ t) ^ B := by
    have h := ENNReal.rpow_le_rpow (autocorrelation_geometric_le μ hf hg d ha hb hab x) hp.le
    simpa only [R, F, H, ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, hAs, hBt] using h
  have hfR := (measurable_autocorrelation_of_aemeasurable μ d hf).pow_const s
  have hgR := (measurable_autocorrelation_of_aemeasurable μ d hg).pow_const t
  have hl := (lintegral_mono (μ := cubeMeasure μ d) hpw).trans
    (ENNReal.lintegral_mul_norm_pow_le hfR.aemeasurable hgR.aemeasurable hA hB hAB)
  let k := 1 / (2 : ℝ) ^ d
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hpow := ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow hl (one_div_nonneg.mpr hp.le)) hk
  have ea : A * (1/p) * k = 1 / s * k * a := by dsimp [A]; field_simp
  have eb : B * (1/p) * k = 1 / t * k * b := by dsimp [B]; field_simp
  unfold gowers lp
  simpa only [F, H, R, ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ENNReal.mul_rpow_of_nonneg _ _ hk, ← ENNReal.rpow_mul, ea, eb, k] using hpow

/-- The source's transformed input exponent in the ordinary Gowers estimate. -/
def ordinaryInputPower (d : ℕ) (p : ℝ) : ℝ := p * (d + 1) / (d + p)

omit [AddCommGroup G] [MeasurableAdd₂ G] [SigmaFinite μ] [μ.IsAddLeftInvariant] in
/-- The transformed input has the same critical moment as the original
function, with equality also for an infinite moment. -/
theorem transformed_critical_moment (d : ℕ) {p : ℝ} (hp : 0 < p) (f : G → ℝ≥0) :
    (∫⁻ x, (↑(f x ^ ordinaryInputPower d p) : ℝ≥0∞) ^ criticalExponent d 1 ∂μ) =
      ∫⁻ x, (f x : ℝ≥0∞) ^ criticalExponent d p ∂μ := by
  have hu : 0 ≤ ordinaryInputPower d p := by unfold ordinaryInputPower; positivity
  simp_rw [ENNReal.coe_rpow_of_nonneg _ hu, ← ENNReal.rpow_mul]
  have h : ordinaryInputPower d p * criticalExponent d 1 = criticalExponent d p := by
    unfold ordinaryInputPower criticalExponent; field_simp
  rw [h]

omit [SigmaFinite μ] in
/-- For `p ≥ 1`, a near-extremiser for the normalized Lebesgue inequality
is a near-extremiser for the ordinary Gowers inequality after the specified
power change. The exponent of the ordinary Gowers quantity is exactly `1/p`. -/
theorem stability_reduction_ge_one (d : ℕ) {p : ℝ} (hp : 1 ≤ p)
    {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (hN : (∫⁻ x, (f x : ℝ≥0∞) ^ criticalExponent d p ∂μ) = 1) :
    gowers μ d p f ≤ (ordinaryGowers μ d (fun x => f x ^ ordinaryInputPower d p)) ^ (1/p) := by
  let b := p / (d + p)
  let a := 1 / p
  let V := fun x => f x ^ b
  let U := fun x => f x ^ ordinaryInputPower d p
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha : 0 < a := one_div_pos.mpr hp'
  have ha' : a ≤ 1 := (div_le_one hp').mpr hp
  have hb : 0 < b := div_pos hp' (by positivity)
  have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha'
  have hu : 0 ≤ ordinaryInputPower d p := by unfold ordinaryInputPower; positivity
  have hfV : AEMeasurable V μ := hf.pow_const _
  have hfU : AEMeasurable U μ := hf.pow_const _
  have hV : (∫⁻ x, (V x : ℝ≥0∞) ^ (2 ^ d : ℕ) ∂μ) = 1 := by
    refine Eq.trans ?_ hN
    apply lintegral_congr
    intro x
    dsimp only [V]
    rw [ENNReal.coe_rpow_of_nonneg _ hb.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    dsimp [b, criticalExponent]; push_cast; ring
  have hID : (fun x => U x ^ a * V x ^ (1-a)) = f := by
    funext x
    dsimp only [U,V]
    rw [← NNReal.rpow_mul, ← NNReal.rpow_mul,
      ← NNReal.rpow_add_of_nonneg _ (mul_nonneg hu ha.le) (mul_nonneg hb.le h1a)]
    suffices ordinaryInputPower d p * a + b * (1 - a) = 1 by rw [this, NNReal.rpow_one]
    dsimp [ordinaryInputPower,a,b]
    field_simp
    ring
  have hs (h) : autocorrelation μ d f h ^ p ≤ autocorrelation μ d U h := by
    have hR := autocorrelation_geometric_le μ hfU hfV d ha.le h1a (by ring) h
    rw [hID] at hR
    have hrv := (autocorrelation_le_lintegral_pow μ d hfV h).trans_eq hV
    have hRU := hR.trans (mul_le_mul le_rfl (ENNReal.rpow_le_rpow hrv h1a) zero_le zero_le)
    simpa [← ENNReal.rpow_mul, a, hp'.ne'] using ENNReal.rpow_le_rpow hRU hp'.le
  have hmono := lintegral_mono (μ := cubeMeasure μ d) hs
  have hk : 0 ≤ 1 / (2 : ℝ) ^ d := by positivity
  have hpow := ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow hmono ha.le) hk
  unfold ordinaryGowers gowers lp
  simpa only [a, U, ENNReal.rpow_one, div_one, ← ENNReal.rpow_mul,
    mul_comm (1 / p) (1 / (2 : ℝ)^d)] using hpow

/-- For `d/(2^d-1)<p<1`, the second weight of the source interpolation
is strictly positive and controls the transformed ordinary Gowers quantity. -/
theorem stability_reduction_lt_one (d : ℕ) (hd : 2 ≤ d) {p : ℝ}
    (hp : lowerEndpoint d < p) (hp1 : p < 1) {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (hN : (∫⁻ x, (f x : ℝ≥0∞) ^ criticalExponent d p ∂μ) = 1) :
    let θ := (d : ℝ) * (1-p) / (((2 : ℝ)^d - d - 1) * p)
    0 < 1-θ ∧ gowers μ d p f ≤
      (ordinaryGowers μ d (fun x => f x ^ ordinaryInputPower d p)) ^ (1-θ) := by
  let K : ℝ := 2^d
  let D : ℝ := d
  let e := lowerEndpoint d
  let θ := D * (1-p) / ((K-D-1)*p)
  let q := criticalExponent d p
  let t := ordinaryInputPower d p
  let V := fun x => f x ^ q
  let U := fun x => f x ^ t
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (by omega : 0 < d)
  have hK : 1 < K := one_lt_pow₀ (by norm_num) (by omega)
  have he : 0 < e := div_pos hD (sub_pos.mpr hK)
  have hDp : D < p * (K-1) := (div_lt_iff₀ (sub_pos.mpr hK)).mp hp
  have hKD : 0 < K-D-1 := by nlinarith only [hDp, mul_lt_mul_of_pos_right hp1 (sub_pos.mpr hK)]
  have hp' : 0 < p := he.trans hp
  have hθ : 0 < θ := div_pos (mul_pos hD (sub_pos.mpr hp1)) (mul_pos hKD hp')
  have hθ' : θ < 1 := (div_lt_one (mul_pos hKD hp')).mpr (by linarith only [hDp])
  have hθb : 0 ≤ 1-θ := sub_nonneg.mpr hθ'.le
  have hq : 0 ≤ q := by dsimp [q,criticalExponent]; positivity
  have ht : 0 ≤ t := by dsimp [t,ordinaryInputPower]; positivity
  have hDp' : 0 < D+p := add_pos hD hp'
  have hrel : 1/p = θ/e + (1-θ)/1 := by
    change 1/p = (D*(1-p)/((K-D-1)*p)) / (D/(K-1)) + (1- D*(1-p)/((K-D-1)*p))/1
    field_simp [hD.ne',hKD.ne',hp'.ne',(sub_pos.mpr hK).ne']; ring
  have hsplit : q*θ + t*(1-θ) = 1 := by
    change (K*p/(D+p))*(D*(1-p)/((K-D-1)*p)) +
      (p*(D+1)/(D+p))*(1-D*(1-p)/((K-D-1)*p)) = 1
    field_simp [hp'.ne',hKD.ne',hDp'.ne']; ring
  have hID : (fun x => V x ^ θ * U x ^ (1-θ)) = f := by
    funext x
    dsimp only [V,U]
    rw [← NNReal.rpow_mul, ← NNReal.rpow_mul,
      ← NNReal.rpow_add_of_nonneg _ (mul_nonneg hq hθ.le) (mul_nonneg ht hθb), hsplit,
      NNReal.rpow_one]
  have hV := lebesgue_lower_endpoint μ d (by omega) (f := V) (hf.pow_const q)
  have hones : lp μ 1 (liftNN V) = 1 := by
    simpa only [lp, liftNN, V, ENNReal.coe_rpow_of_nonneg _ hq, ENNReal.rpow_one, div_one]
      using hN
  have hV' : gowers μ d e V ^ θ ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow (hV.trans_eq hones) hθ.le
  have h := gowers_geometric_le μ d (f := V) (g := U) (hf.pow_const q) (hf.pow_const t)
    hθ.le hθb (by ring) hp' he zero_lt_one hrel
  rw [hID] at h
  exact ⟨sub_pos.mpr hθ', h.trans ((mul_le_mul hV' le_rfl zero_le zero_le).trans_eq (one_mul _))⟩

end LpGowers
