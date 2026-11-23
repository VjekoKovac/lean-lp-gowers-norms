module

public import LpGowers.YoungScaling
public import LpGowers.YoungNormalization
public import LpGowers.IndicatorInverse
public import LpGowers.IndicatorCoset

/-! # Theorem 1.2 of Kovač and Rogers

The inverse theorem for the identical-input Young inequality combines
Hölder stability and a normalized plateau with the indicator inverse theorem.
The ordinary Gowers inverse theorem and then the general inverse theorem
follow by the power changes of Eisner–Tao and Kovač–Rogers.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

private theorem near_moment_transfer {d κ e δ : ℝ} (hd : 1 ≤ d)
    (hκ1 : κ < 1) (he : 0 ≤ e) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbudget : (1-κ)^(1/d) + 2*e ≤ 1-δ) {A B : ℝ≥0∞}
    (hf : ENNReal.ofReal (1-δ) ≤ A)
    (hlip : A^(1/d) ≤ B^(1/d)+2*ENNReal.ofReal e) :
    ENNReal.ofReal (1-κ) ≤ B := by
  let β := (1-κ)^(1/d)
  have hd' : 0 < d := zero_lt_one.trans_le hd
  have hβ : 0 < β := Real.rpow_pos_of_pos (sub_pos.mpr hκ1) _
  have hexp : 1/d ≤ 1 := (div_le_one hd').mpr hd
  have hroot : ENNReal.ofReal (1-δ) ≤ A^(1/d) := by
    refine (ENNReal.ofReal_le_ofReal (Real.self_le_rpow_of_le_one (sub_nonneg.mpr hδ1.le)
      (by linarith) hexp)).trans ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hδ1.le) (one_div_nonneg.mpr hd'.le)]
    exact ENNReal.rpow_le_rpow hf (one_div_nonneg.mpr hd'.le)
  have hB : ENNReal.ofReal β ≤ B^(1/d) := by
    by_cases hinf : B^(1/d) = ⊤
    · rw [hinf]; exact le_top
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hinf,
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩) (hroot.trans hlip)
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1.le),ENNReal.toReal_add hinf (by finiteness),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal he] at h
    norm_num only [ENNReal.toReal_ofNat] at h
    apply ENNReal.ofReal_le_of_le_toReal
    change β+2*e ≤ 1-δ at hbudget
    linarith
  have h := ENNReal.rpow_le_rpow hB hd'.le
  rw [ENNReal.ofReal_rpow_of_nonneg hβ.le hd'.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hd'.ne', ENNReal.rpow_one] at h
  simpa only [β,← Real.rpow_mul (sub_nonneg.mpr hκ1.le),one_div_mul_cancel hd'.ne',
    Real.rpow_one] using h

/-- The nonnegative identical-input inverse Young theorem for integer output
exponents, including quantitative approximation by a normalized compact open coset. -/
theorem diagonalInverseYoung.{u} : DiagonalInverseYoung.{u} := by
  classical
  intro d hd η hη
  let s := 2*(d:ℝ)/(d+1)
  have hD : 1 ≤ (d:ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hs : 1 ≤ s := (le_div_iff₀ (by positivity : 0 < (d:ℝ)+1)).mpr (by linarith)
  obtain ⟨r,hr,close⟩ := normalized_indicator_close_coset (s := s) hs (η/2) (half_pos hη)
  obtain ⟨κ,hκ,hκ1,inverse⟩ := indicator_inverse_young.{u} d hd r hr
  let β := (1-κ)^(1/(d:ℝ))
  have hβ : β < 1 := Real.rpow_lt_one (by linarith) (by linarith) (by positivity)
  let t := (1-β)/4
  have ht : 0 < t := by dsimp [t]; linarith
  let e := min (η/2) t
  have he : 0 < e := lt_min (half_pos hη) ht
  obtain ⟨ζ,hζ,hζ1,flat⟩ := exists_unit_young_indicator.{u} d hd e he
  let δ := min ζ t
  have hδ : 0 < δ := lt_min hζ ht
  have hδ1 : δ < 1 := (min_le_left ..).trans_lt hζ1
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf _ hfm hnear
  obtain ⟨E,hE,hEp,hEf,hgm,dist⟩ := flat G μ f hf hfm
    ((ENNReal.ofReal_le_ofReal (sub_le_sub_left (show δ ≤ ζ from min_le_left ..) _)).trans hnear)
  let g := unitIndicator μ s E
  have hg : Measurable g := measurable_unitIndicator μ hE s
  let moment := fun (F : G → ℝ≥0) => ∫⁻ a, (∫⁻ x, (F x : ℝ≥0∞)* F (x+a) ∂μ)^(d:ℝ) ∂μ
  have hL := diagonalYoung_lp_le μ d hd f g hf hg.aemeasurable hfm hgm
  change moment f ^ (1/(d:ℝ)) ≤ moment g ^ (1/(d:ℝ)) + 2*lpDist μ s f g at hL
  have hL' := hL.trans (add_le_add_right (mul_le_mul_right dist 2) _)
  have budget : β+2*e ≤ 1-δ := by
    have he' : e ≤ t := min_le_right ..
    have hδ' : δ ≤ t := min_le_right ..
    dsimp [t] at he' hδ'
    linarith
  have good : ENNReal.ofReal (1-κ) ≤ moment g :=
    near_moment_transfer hD hκ1 he.le hδ hδ1 budget hnear hL'
  have hrect := mul_le_mul_right good ((μ E)^(d+1))
  rw [mul_comm _ (ENNReal.ofReal (1-κ))] at hrect
  have scale := indicator_moment_rescale μ d (by omega) E hEp hEf
  change _ = (μ E)^(d+1)*moment g at scale
  obtain ⟨H,x₀,hc,ho,hDiff,hMass⟩ := inverse G μ E hE hEp hEf (hrect.trans_eq scale.symm)
  have last := close G μ E H x₀ hE hEp hEf hc ho hDiff hMass
  let v := cosetProfile μ s 1 H x₀
  have hv : Measurable v := Measurable.ite ((measurable_id.sub_const x₀) ho.measurableSet)
    measurable_const measurable_const
  refine ⟨H,x₀,hc,ho,(lpDist_triangle μ hs f g v hf hg.aemeasurable hv.aemeasurable).trans ?_⟩
  refine (add_le_add dist last).trans ?_
  rw [← ENNReal.ofReal_add he.le (half_pos hη).le]
  apply ENNReal.ofReal_le_ofReal
  linarith only [show e ≤ η/2 from min_le_left ..]

/-- The full Lebesgue estimate and uniform near-extremiser statement of
Theorem 1.2, for the complete source ranges of `d` and `p`. -/
theorem lebesgueEstimate.{u} : LebesgueEstimate.{u} :=
  lebesgueEstimate_iff_ordinaryInverse.mpr (ordinaryInverse_of_diagonalInverseYoung diagonalInverseYoung)

end LpGowers
