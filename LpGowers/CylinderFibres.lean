module

public import LpGowers.LWFactorization
public import LpGowers.DegreeNear
import Mathlib.Tactic

/-! # Slicing a tensor close to a constant on a set

This is the fibre-selection step of Lemma 6.1. The averaging uses the
product of the other coordinate densities as a probability density. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LpGowers

/-- A tensor which approximates a scaled indicator has a scaled-indicator
approximation to each coordinate factor, obtained on a single measurable
fibre of the original set. -/
theorem select_indicator_fibre {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} {Ω : Set (Fin (n+1) → X)} (hΩ : MeasurableSet Ω)
    (r : Fin (n+1) → X → ℝ≥0∞) (hr : ∀ i, Measurable (r i))
    (hn : ∀ i, (∫⁻ x, r i x ∂μ) = 1) {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤)
    {κ : ℝ≥0∞}
    (hnear : l1DensityError (cubeMeasure μ (n+1)) (fun x => ∏ i, r i (x i))
      (Ω.indicator (fun _ => c)) < κ) (v : Fin (n+1)) :
    ∃ (A : Set X) (b : ℝ≥0∞), MeasurableSet A ∧ b ≠ 0 ∧ b ≠ ⊤ ∧
      l1DensityError μ (r v) (A.indicator (fun _ => b)) ≤ κ := by
  classical
  let ν := cubeMeasure μ n
  let Q := fun y : Fin n → X => ∏ j : Fin n, r (v.succAbove j) (y j)
  let F := fun x : Fin (n+1) → X => ∏ i, r i (x i)
  let H := Ω.indicator (fun _ => c)
  let D := fun x => (F x-H x)+(H x-F x)
  have hQ : Measurable Q := Finset.measurable_prod _ (fun j _ => (hr _).comp (measurable_pi_apply j))
  have hQn : (∫⁻ y, Q y ∂ν) = 1 := by
    simpa only [Q,ν,hn,Finset.prod_const_one] using
      lintegral_pi_separated μ n (fun j => r (v.succAbove j)) (fun j => hr _)
  have hF : Measurable F := Finset.measurable_prod _ (fun i _ => (hr i).comp (measurable_pi_apply i))
  have hH : Measurable H := measurable_const.indicator hΩ
  have hD : Measurable D := (hF.sub hH).add (hH.sub hF)
  let d := fun y : Fin n → X => ∫⁻ a, D (v.insertNth a y) ∂μ
  have hd : (∫⁻ y, d y ∂ν) < κ := (lintegral_insertCoord μ v hD).symm.le.trans_lt hnear
  have good : ∃ y, Q y ≠ 0 ∧ Q y ≠ ⊤ ∧ d y ≤ κ * Q y := by
    by_contra! bad
    have h := ae_lt_top hQ (by simp [hQn] : (∫⁻ y, Q y ∂ν) ≠ ⊤)
    have h' : ∀ᵐ y ∂ν, κ * Q y ≤ d y := by
      filter_upwards [h] with y hy
      by_cases hz : Q y=0
      · simp [hz]
      · exact (bad y hz hy.ne).le
    have ht : κ ≤ ∫⁻ y, d y ∂ν := by
      simpa only [lintegral_const_mul κ hQ, hQn, mul_one] using lintegral_mono_ae h'
    exact hd.not_ge ht
  obtain ⟨y,hy,hy',hgood⟩ := good
  let ins := fun a : X => v.insertNth (α := fun _ => X) a y
  have hmi : Measurable ins := (measurable_insertCoord v).comp (measurable_id.prodMk measurable_const)
  let A := ins ⁻¹' Ω
  let b := c / Q y
  have hb : b ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hc,hy'⟩
  have hb' : b ≠ ⊤ := ENNReal.div_ne_top hc' hy
  have hmA : MeasurableSet A := hmi hΩ
  refine ⟨A,b,hmA,hb,hb',?_⟩
  have hsplit (a : X) : F (ins a) = Q y * r v a := by
    simp only [F,ins,Fin.prod_univ_succAbove (fun i => r i _) v, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, Q, mul_comm]
  have hi (a : X) : H (ins a) = Q y * A.indicator (fun _ => b) a := by
    by_cases h : a ∈ A
    · have h' : ins a ∈ Ω := h
      simp [H,h',h,b,ENNReal.mul_div_cancel hy hy']
    · have h' : ins a ∉ Ω := h
      simp [H,h',h]
  have heq : d y = Q y * l1DensityError μ (r v) (A.indicator (fun _ => b)) := by
    rw [← l1DensityError_scale μ (hr v) (measurable_const.indicator hmA) _ hy']
    apply lintegral_congr
    intro a
    change (F (ins a)-H (ins a)) + (H (ins a)-F (ins a)) = _
    rw [hsplit,hi]
  rw [heq,mul_comm κ] at hgood
  exact (ENNReal.mul_le_mul_iff_right hy hy').mp hgood

/-- Normalizing the height on a selected fibre preserves the approximation
and gives the fibre positive finite measure. -/
theorem normalize_indicator_fibre {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) {r : X → ℝ≥0∞} (hr : Measurable r)
    (hn : (∫⁻ x, r x ∂μ) = 1) {b κ : ℝ≥0∞} (hb : b ≠ 0) (_hb' : b ≠ ⊤)
    (hκ : κ < 1) (hd : l1DensityError μ r (A.indicator (fun _ => b)) ≤ κ) :
    μ A ≠ 0 ∧ μ A ≠ ⊤ ∧ l1DensityError μ r (A.indicator (fun _ => (μ A)⁻¹)) ≤ 3*κ := by
  let B := A.indicator (fun _ => b)
  let C := A.indicator (fun _ => (μ A)⁻¹)
  have hB : Measurable B := measurable_const.indicator hA
  have hC : Measurable C := measurable_const.indicator hA
  have hm : (∫⁻ x, B x ∂μ) = b * μ A := lintegral_indicator_const hA _
  have hlo : 1 - b * μ A ≤ κ := by
    rw [← hm]
    exact (one_sub_lintegral_le_l1 μ hr hB hn).trans hd
  have hhi : b * μ A - 1 ≤ κ := by
    rw [← hm, ← hn]
    exact (lintegral_sub_le r B hr).trans ((lintegral_mono
      (fun x => le_add_left (le_refl (B x - r x)))).trans hd)
  have hz : μ A ≠ 0 := by rintro h; simp [h] at hlo; exact hκ.not_ge hlo
  have ht : μ A ≠ ⊤ := by
    rintro h
    simp [h, ENNReal.mul_top hb] at hhi
    exact hκ.not_ge (by simp [hhi])
  have hscale : (μ A)⁻¹ * μ A = 1 := ENNReal.inv_mul_cancel hz ht
  have hdiff : l1DensityError μ B C = (b * μ A - 1) + (1 - b * μ A) := by
    have hp (x) : (B x-C x)+(C x-B x) = A.indicator (fun _ => (b-(μ A)⁻¹)+((μ A)⁻¹-b)) x := by
      by_cases hx : x ∈ A <;> simp [B,C,hx]
    simp only [l1DensityError, hp, lintegral_indicator_const hA, add_mul,
      ENNReal.sub_mul (fun _ _ => ht), hscale]
  refine ⟨hz,ht, (l1DensityError_triangle μ hr hB hC).trans ?_⟩
  rw [hdiff]
  exact (add_le_add hd (add_le_add hhi hlo)).trans_eq (by ring)

end LpGowers
