module

public import LpGowers.DiscreteSampleLimit
public import LpGowers.Euclidean

/-! Matching the logarithmic large-side correction to the exact
one-dimensional Gaussian value, as in §8. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace LpGowers.Discrete

/-- The sharp Euclidean constant gives exactly the coefficient in (1.13). -/
theorem log_sharp_constant (d p : ℕ) (hp : 0 < p) :
    (2:ℝ)^d*(p:ℝ)*logTwo (sharpEuclideanConstant d 1 p) = -correction d p := by
  have hpos : 0 < (p:ℝ) := by exact_mod_cast hp
  have hsum : 0 < (d:ℝ)+p := by positivity
  unfold sharpEuclideanConstant correction logTwo
  push_cast
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_rpow_eq_mul_logb_of_pos hpos,Real.logb_rpow_eq_mul_logb_of_pos hsum,
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), pow_succ]
  push_cast
  field_simp
  ring

/-- A near-optimal Gaussian test provides the lower correction up to
any prescribed additive logarithmic tolerance. -/
theorem gaussian_log_test (d p : ℕ) (hp : 0 < p) {η : ℝ} (hη : 0 < η) :
    let N := (2:ℝ)^d*(p:ℝ)
    let D := ((d+p:ℕ):ℝ)
    let q := criticalExponent d p
    ∃ r : ℝ, 0 < r ∧ r < sharpEuclideanConstant d 1 p ∧
      ∀ U L : ℝ≥0∞, 0<L → L<⊤ → U<⊤ → ENNReal.ofReal r*L < U →
        0 < (U^N).toReal ∧ 0 < (L^q).toReal ∧
          -correction d p-η ≤ logTwo ((U^N).toReal) - D*logTwo ((L^q).toReal) := by
  intro N D q
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hN : 0 < N := by dsimp [N]; positivity
  let C := sharpEuclideanConstant d 1 p
  have hC : 0 < C := by dsimp [C,sharpEuclideanConstant]; positivity
  let r := C / (2:ℝ)^(η/N)
  have hB : 1 < (2:ℝ)^(η/N) := Real.one_lt_rpow (by norm_num) (div_pos hη hN)
  have hr : 0 < r := div_pos hC (by linarith)
  refine ⟨r,hr,div_lt_self hC hB,?_⟩
  intro U L hL hLt hUt hu
  have hU : 0 < U := zero_le.trans_lt hu
  have hL' := ENNReal.toReal_pos hL.ne' hLt.ne
  have hU' := ENNReal.toReal_pos hU.ne' hUt.ne
  have he := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLt.ne) hUt.ne).mpr hu
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le] at he
  have hlog := (Real.strictMonoOn_logb (b := 2) (by norm_num))
    (mul_pos hr hL') hU' he
  rw [Real.logb_mul hr.ne' hL'.ne'] at hlog
  have ec : logTwo r = logTwo C - η/N := by
    dsimp [r,logTwo]; rw [Real.logb_div hC.ne' (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  have hqD : D*q=N := by
    have hden : (d:ℝ)+p ≠ 0 := (by positivity : 0 < (d:ℝ)+p).ne'
    dsimp [D,q,criticalExponent,N]
    push_cast
    field_simp
  simp only [← ENNReal.toReal_rpow]
  refine ⟨Real.rpow_pos_of_pos hU' _, Real.rpow_pos_of_pos hL' _, ?_⟩
  unfold logTwo
  rw [Real.logb_rpow_eq_mul_logb_of_pos hU', Real.logb_rpow_eq_mul_logb_of_pos hL', ← mul_assoc,hqD]
  change logTwo r + logTwo L.toReal < logTwo U.toReal at hlog
  rw [ec] at hlog
  have hCval : N*logTwo C = -correction d p := log_sharp_constant d p hp
  have hηid : N*(η/N)=η := by field_simp
  change -correction d p-η ≤ N*logTwo U.toReal -N*logTwo L.toReal
  nlinarith only [mul_pos hN (sub_pos.mpr hlog), hCval, hηid]

end LpGowers.Discrete
