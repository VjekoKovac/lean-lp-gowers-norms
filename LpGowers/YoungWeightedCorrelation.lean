module

public import LpGowers.YoungScalarProfiles
public import LpGowers.YoungKernelCompact
import Mathlib.Tactic

/-! The two weighted convolution branches in the Young Euler derivative
at a centered Gaussian are compact. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LpGowers
set_option backward.isDefEq.respectTransparency false
section
variable {n : ℕ} {r v w s : ℝ≥0∞}
local notation "ν" => euclideanMeasure n
variable [Fact (1≤r)] [Fact (1≤v)] [Fact (1≤w)] [Fact (1≤s)]
  [w.HolderConjugate r] [s.HolderConjugate v]

/-- Multiplication by a Gaussian weight localizes both branches of the
linearized outer correlation. The finite conjugate exponents are explicit. -/
theorem compact_gaussian_correlation_branches
    (hr : r≠∞) (hw : w≠∞) (hs : s≠∞)
    (B : Lp ℝ v ν →L[ℝ] Lp ℝ r ν →L[ℝ] Lp ℝ w ν)
    (hB : ∀ H F, B H F =ᵐ[ν] fun x => ∫ y, H y * F (y+x) ∂ν)
    (D : Lp ℝ w ν →L[ℝ] Lp ℝ r ν) {J : Rn n → ℝ}
    (hD : ∀ u, D u =ᵐ[ν] fun x => J x * u x) (hJ : IsYoungProfile J)
    (G : Lp ℝ r ν) (U : Lp ℝ v ν) (hG : IsYoungProfile G) (hU : IsYoungProfile U) :
    IsCompactOperator (D.comp (B U)) ∧ IsCompactOperator (D.comp (B.flip G)) := by
  let : (euclideanMeasure n).IsAddRightInvariant := by
    change (volume : Measure (Rn n)).IsAddRightInvariant
    infer_instance
  have hJm := hJ.memLp ((zero_lt_one.trans_le (Fact.out : 1≤r)).ne') hr
  constructor
  · apply isCompactOperator_of_weighted_reversed_kernel (p':=w) hw hr
      (hU.memLp ((zero_lt_one.trans_le (Fact.out : 1≤w)).ne') hw) hJm
    intro F
    filter_upwards [hD (B U F),hB U F] with x hx hx'
    change D (B U F) x = _
    rw [hx,hx']
    congr 1
    change (∫ y : Rn n, U y * F (y+x) ∂ν) = (∫ y : Rn n, U (y-x) * F y ∂ν)
    have h := integral_add_right_eq_self (μ := ν) (fun y => U (y-x) * F y) x
    simpa! only [add_sub_cancel_right] using h
  · apply isCompactOperator_of_weighted_correlation (p':=s) hs hr
      (hG.memLp ((zero_lt_one.trans_le (Fact.out : 1≤s)).ne') hs) hJm
    intro H
    filter_upwards [hD (B H G),hB H G] with x hx hx'
    change D (B H G) x = _
    rw [hx,hx']
    congr 1
    exact integral_congr_ae (ae_of_all _ fun y => by dsimp only; rw [add_comm x y,mul_comm])

end
end LpGowers
