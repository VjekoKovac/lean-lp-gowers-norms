module

public import LpGowers.YoungChangeVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-! # Sharp Euclidean Young from geometric Brascamp–Lieb

Use the three coisometries in `YoungFrame` with the dual test function
scaled by `2a`. The Jacobian identity in `YoungChangeVariables` gives the
sharp trilinear constant in every dimension.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace LpGowers

abbrev YoungHilbert (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev YoungPair (n : ℕ) := WithLp 2 (YoungHilbert n × YoungHilbert n)

/-- The single geometric Brascamp--Lieb datum needed for the Young estimate. -/
def YoungFrameBound (n : ℕ) (s : ℝ) : Prop :=
  ∀ U : Fin 3 → YoungHilbert n → ℝ≥0∞, (∀ i, Measurable (U i)) →
    (∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i) ≤
      ∏ i, (∫⁻ x, U i x)^youngFrameWeight s i

private def coord (n : ℕ) : YoungHilbert n → Rn n := WithLp.ofLp

private theorem coord_preserving (n : ℕ) :
    MeasurePreserving (coord n) volume (euclideanMeasure n) := PiLp.volume_preserving_ofLp (Fin n)

private theorem pair_coord_preserving (n : ℕ) :
    MeasurePreserving (fun z : YoungPair n => (coord n z.fst,coord n z.snd))
      volume ((euclideanMeasure n).prod (euclideanMeasure n)) :=
  ((coord_preserving n).prod (coord_preserving n)).comp
    (WithLp.volume_preserving_ofLp (YoungHilbert n) (YoungHilbert n))

theorem sharpYoungTrilinear_of_frame (n : ℕ) (hframe : ∀ s : ℝ, 1<s → YoungFrameBound n s) :
    SharpYoungTrilinear n := by
  classical
  intro s hs F G H hF hG hH μ
  let q := 2*s/(s+1)
  let r := s/(s-1)
  let w := (s+1)/(2*s)
  let v := (s-1)/s
  let a := youngFrameA s
  let b := youngFrameB s
  have hs₀ := zero_lt_one.trans hs
  have hs₁ := sub_pos.mpr hs
  have hw : 0<w := by dsimp [w]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have hqw : q*w=1 := by dsimp [q,w]; field_simp
  have hrv : r*v=1 := by dsimp [r,v]; field_simp
  have hq : 1/q = w := by dsimp [q,w]; simp
  have hr : 1/r = v := by dsimp [r,v]; simp
  let U₀ := fun y : YoungHilbert n => F (coord n y)^q
  let U₁ := fun y : YoungHilbert n => G (coord n y)^q
  let U₂ := fun y : YoungHilbert n => H ((2*a) • coord n y)^r
  let U : Fin 3 → YoungHilbert n → ℝ≥0∞ := ![U₀,U₁,U₂]
  have hcoord := (coord_preserving n).measurable
  have hU : ∀ i, Measurable (U i) := by
    intro i; fin_cases i
    · exact (hF.comp hcoord).pow_const q
    · exact (hG.comp hcoord).pow_const q
    · exact (hH.comp (hcoord.const_smul (2*a))).pow_const r
  let P := fun z : Rn n × Rn n =>
    F ((-a) • z.1+b • z.2) * G (a • z.1+b • z.2) * H ((2*a) • z.1)
  have hP : Measurable P := by dsimp [P]; fun_prop
  have point (z : YoungPair n) :
      ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i =
        P (coord n z.fst,coord n z.snd) := by
    rw [Fin.prod_univ_three]
    change (F (coord n ((-a) • z.fst+b • z.snd))^q)^w *
      (G (coord n (a • z.fst+b • z.snd))^q)^w *
      (H ((2*a) • coord n ((1:ℝ) • z.fst + (0:ℝ) • z.snd))^r)^v = _
    simp only [← ENNReal.rpow_mul,hqw,hrv,ENNReal.rpow_one,one_smul,zero_smul,add_zero]
    rfl
  have hu₀ : (∫⁻ y, U₀ y)^w = lp μ q F := by
    rw [lp,hq,← (coord_preserving n).lintegral_comp (hF.pow_const q)]
  have hu₁ : (∫⁻ y, U₁ y)^w = lp μ q G := by
    rw [lp,hq,← (coord_preserving n).lintegral_comp (hG.pow_const q)]
  have hu₂ : (∫⁻ y, U₂ y)^v = (youngDilation n (2*a))^v * lp μ r H := by
    have h := (coord_preserving n).lintegral_comp ((hH.comp (measurable_const_smul (2*a))).pow_const r)
    change (∫⁻ y, U₂ y) = ∫⁻ y, H ((2*a) • y)^r ∂μ at h
    rw [h,show (∫⁻ y, H ((2*a) • y)^r ∂μ) = youngDilation n (2*a) * ∫⁻ y, H y^r ∂μ from
      young_lintegral_smul n (by positivity) (fun y => H y^r) (hH.pow_const r),
      ENNReal.mul_rpow_of_nonneg _ _ hv.le,lp,hr]
  have J := hframe s hs U hU
  simp_rw [point] at J
  rw [(pair_coord_preserving n).lintegral_comp hP,Fin.prod_univ_three] at J
  change (∫⁻ z, P z ∂μ.prod μ) ≤ (∫⁻ y, U₀ y)^w * (∫⁻ y, U₁ y)^w * (∫⁻ y, U₂ y)^v at J
  rw [hu₀,hu₁,hu₂] at J
  have J' := young_frame_change_variables n ha hb F G H hF hG hH
  dsimp only at J'
  change (∫⁻ z, P z ∂μ.prod μ) = _ at J'
  rw [J'] at J
  let k := youngDilation n b * youngDilation n (2*a)
  have k0 : k ≠ 0 := by dsimp [k,youngDilation]; positivity
  have kt : k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have T := mul_le_mul_right J k⁻¹
  change k⁻¹*(k*_) ≤ _ at T
  rw [← mul_assoc,ENNReal.inv_mul_cancel k0 kt,one_mul] at T
  refine T.trans_eq ?_
  rw [← young_dilation_constant n s hs]
  dsimp only [k,a,b,v,q,r]
  ac_rfl

end LpGowers
