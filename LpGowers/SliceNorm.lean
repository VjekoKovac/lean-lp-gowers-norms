module

public import LpGowers.DegreeProofs
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Controlling the cubic Gowers norm on a two-dimensional slice

The second autocorrelation of a selected slice is close in squared integral
to a rectangle indicator. Minkowski's inequality and the marginal identity
bound the cubic Gowers norm appearing in diagonal leakage. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

/-- A squared error of at most one and a comparison function of squared
integral at most four suffice for the uniform cubic prefactor in §6. -/
theorem slice_gowers_three_bound {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    {g : G → ℝ≥0} (hg : AEMeasurable g μ) {I : (Fin 2 → G) → ℝ≥0∞}
    (hI : Measurable I) (hM : (∫⁻ h, (I h)^2 ∂cubeMeasure μ 2) ≤ 4)
    (hE : (∫⁻ h, ((autocorrelation μ 2 g h-I h) + (I h-autocorrelation μ 2 g h))^2
      ∂cubeMeasure μ 2) ≤ 1) :
    (ordinaryGowers μ 3 g)^2 ≤ 2 := by
  let R := autocorrelation μ 2 g
  let D := fun h => (R h-I h)+(I h-R h)
  let ν := cubeMeasure μ 2
  have hR : Measurable R := measurable_autocorrelation_of_aemeasurable μ 2 hg
  have hD : Measurable D := (hR.sub hI).add (hI.sub hR)
  have point (h) : R h ≤ I h + D h := by
    exact (le_add_tsub (a := R h) (b := I h)).trans
      (add_le_add_right (le_self_add : R h-I h ≤ D h) _)
  have lI : lp ν 2 I ≤ 2 := by
    rw [lp,one_div,ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<2)]
    norm_num only [ENNReal.rpow_two]
    exact hM.trans_eq (by norm_num)
  have lD : lp ν 2 D ≤ 1 := by
    rw [lp,one_div,ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<2)]
    simpa only [ENNReal.rpow_two,one_pow] using hE
  have upper : lp ν 2 R ≤ 4 := by
    calc
      _ ≤ lp ν 2 (I+D) := by unfold lp; gcongr with h; exact point h
      _ ≤ lp ν 2 I + lp ν 2 D := ENNReal.lintegral_Lp_add_le hI.aemeasurable hD.aemeasurable (by norm_num)
      _ ≤ 2+1 := add_le_add lI lD
      _ ≤ 4 := by norm_num
  rw [ordinaryGowers,gowers_one_succ_eq_gowers_two μ hg 2,gowers,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num only [Nat.cast_ofNat,show (1/(2:ℝ)^2)*2=(2:ℝ)⁻¹ by norm_num]
  rw [one_div,ENNReal.rpow_inv_le_iff (by norm_num : (0:ℝ)<2),ENNReal.rpow_two]
  exact upper.trans_eq (by norm_num)

end LpGowers
