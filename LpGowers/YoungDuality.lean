module

public import LpGowers.YoungTrilinearDefs
public import LpGowers.YoungContinuity
public import LpGowers.ClosureLeakage

/-! # Duality for the sharp Young estimate

The dual test is the autocorrelation to the power `p-1`. Ordinary Young
first proves finiteness when the input moment is finite, so the cancellation
is valid even for input functions without compact support. At the endpoint
the identity follows directly from translation invariance and Tonelli. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

theorem sharpDiagonalYoung_of_trilinear (n : ℕ) (hY : SharpYoungTrilinear n) :
    SharpDiagonalYoung n := by
  intro p hp f hf
  let μ := euclideanMeasure n
  let F := liftNN f
  let R := pairCorrelation μ F F
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have : μ.IsAddLeftInvariant := by unfold μ euclideanMeasure; infer_instance
  have hmF : Measurable F := hf.coe_nnreal_ennreal
  have hmR : Measurable R := Measurable.lintegral_prod_right ((hmF.comp measurable_snd).mul
    (hmF.comp (measurable_snd.add measurable_fst)))
  rcases eq_or_lt_of_le hp with rfl | hp
  · have hm := pairCorrelation_self_mass μ hf.aemeasurable
    change (∫⁻ t, R t ^ (1:ℝ) ∂μ) ≤ _
    norm_num [diagonalYoungFactor,ENNReal.rpow_two] at *
    exact hm.le
  let s := 2*p/(p+1)
  let r := p/(p-1)
  let A := ∫⁻ x, (F x)^s ∂μ
  let J := ∫⁻ t, (R t)^p ∂μ
  let C := ENNReal.ofReal (diagonalYoungFactor p)^n
  have hp0 : 0<p := zero_lt_one.trans hp
  have ht : 0<p-1 := sub_pos.mpr hp
  have hs : 0<s := by dsimp [s]; positivity
  have hr : 0<r := div_pos hp0 ht
  have hC : 0<C := by
    apply pos_iff_ne_zero.mpr
    apply pow_ne_zero
    apply (ENNReal.ofReal_pos.mpr _).ne'
    unfold diagonalYoungFactor
    positivity
  change J ≤ C*A^(p+1)
  by_cases hAt : A = ⊤
  · simp [hAt,ENNReal.top_rpow_of_pos (show 0<p+1 by linarith),ENNReal.mul_top hC.ne']
  by_cases hJ : J=0
  · simp [hJ]
  have hJt : J ≠ ⊤ := by
    have h := mixedYoung μ hp hmF.aemeasurable hmF.aemeasurable
    change J^(1/p) ≤ A^(1/s) * A^(1/s) at h
    intro ht'
    rw [ht',ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)] at h
    exact (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hs.le) hAt)
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hs.le) hAt)) (top_unique h)
  let H := fun t => R t ^ (p-1)
  have hH : Measurable H := hmR.pow_const _
  have hHnorm : lp μ r H = J^(1/r) := by
    simp only [lp,H,← ENNReal.rpow_mul]
    rw [show (p-1)*r=p by dsimp [r]; field_simp]
  have htest := hY p hp F F H hmF hmF hH
  change (∫⁻ t, R t * H t ∂μ) ≤ C^(1/p)*A^(1/s)*A^(1/s)*lp μ r H at htest
  have hpt (t) : R t * H t = R t ^ p := by
    dsimp [H]
    calc
      _ = (R t)^1 * (R t)^(p-1) := by rw [ENNReal.rpow_one]
      _ = (R t)^(1+(p-1)) := (ENNReal.rpow_add_of_nonneg _ _ (by norm_num) ht.le).symm
      _ = _ := by congr 1; ring
  simp_rw [hpt] at htest
  rw [hHnorm] at htest
  have hsum : 1/p+1/r=1 := by dsimp [r]; field_simp; ring
  have hsplit : J^(1/p) * J^(1/r)=J := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (one_div_nonneg.mpr hp0.le) (one_div_nonneg.mpr hr.le),
      hsum,ENNReal.rpow_one]
  have hJn : J^(1/r)≠0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hJ) hJt).ne'
  have hJf : J^(1/r)≠⊤ := ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hr.le) hJt
  have hroot : J^(1/p) ≤ C^(1/p)*A^(1/s)*A^(1/s) := by
    apply (ENNReal.mul_le_mul_iff_left hJn hJf).mp
    rw [hsplit]
    exact htest
  have h := ENNReal.rpow_le_rpow hroot hp0.le
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,← ENNReal.rpow_mul,
    one_div_mul_cancel hp0.ne',ENNReal.rpow_one,mul_assoc] at h
  have he : 1/s*p + 1/s*p = p+1 := by dsimp [s]; field_simp; ring
  rwa [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),he] at h

end LpGowers
