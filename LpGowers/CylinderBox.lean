module

public import LpGowers.CylinderFibres
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # From a tensor approximation to a box

Once the normalized indicator is close to a tensor density, choose one fibre
in each coordinate, normalize its height, and multiply the resulting probability
densities. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators symmDiff
namespace LpGowers

private theorem diff_le_of_indicator_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (h0 : μ S ≠ 0) (ht : μ S ≠ ⊤)
    {e : ℝ} (he : 0 ≤ e)
    (H : l1DensityError μ (S.indicator (fun _ => (μ S)⁻¹))
      (T.indicator (fun _ => (μ T)⁻¹)) ≤ ENNReal.ofReal e) :
    μ.real (S \ T) ≤ e * μ.real S := by
  have Q : (μ S)⁻¹ * μ (S \ T) ≤ ENNReal.ofReal e := by
    rw [← lintegral_indicator_const (hS.diff hT) ((μ S)⁻¹)]
    apply le_trans _ H
    apply lintegral_mono
    intro x
    by_cases hs : x ∈ S <;> by_cases ht' : x ∈ T <;>
      simp [hs, ht']
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top Q
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal he, inv_mul_eq_div] at h
  exact (div_le_iff₀ (ENNReal.toReal_pos h0 ht)).mp h

/-- Relative symmetric difference from the `L¹` distance of the two uniform
probability measures. The estimate applies at any tolerance up to one half. -/
theorem symmDiff_of_indicator_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (hs0 : μ S ≠ 0) (hst : μ S ≠ ⊤)
    (ht0 : μ T ≠ 0) (htt : μ T ≠ ⊤) {e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1/2)
    (H : l1DensityError μ (S.indicator (fun _ => (μ S)⁻¹))
      (T.indicator (fun _ => (μ T)⁻¹)) ≤ ENNReal.ofReal e) :
    μ.real (S ∆ T) ≤ 3*e*μ.real S := by
  have hA := diff_le_of_indicator_error μ hS hT hs0 hst he H
  have H' := (l1DensityError_comm μ _ _).symm.le.trans H
  have hB := diff_le_of_indicator_error μ hT hS ht0 htt he H'
  have hi := measureReal_sdiff_add_inter (μ := μ) (s := T) hS htt
  have hint : μ.real (T ∩ S) ≤ μ.real S := measureReal_mono inter_subset_right hst
  have hBT : μ.real T ≤ 2 * μ.real S := by
    nlinarith [mul_le_mul_of_nonneg_right he' (measureReal_nonneg (μ := μ) (s := T))]
  rw [measureReal_symmDiff_eq hS hT hst htt]
  nlinarith only [hA,hB,mul_le_mul_of_nonneg_left hBT he]

/-- A uniform probability on a set that is close to an independent product
is supported, up to small relative symmetric difference, on a measurable box.
The threshold depends only on dimension and target error. -/
theorem box_of_uniform_tensor (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (Ω : Set (Fin (n+1) → X)), MeasurableSet Ω →
      (cubeMeasure μ (n+1)) Ω ≠ 0 → (cubeMeasure μ (n+1)) Ω ≠ ⊤ →
    ∀ r : Fin (n+1) → X → ℝ≥0∞, (∀ i, Measurable (r i)) → (∀ i, (∫⁻ x, r i x ∂μ) = 1) →
    l1DensityError (cubeMeasure μ (n+1))
      (Ω.indicator (fun _ => ((cubeMeasure μ (n+1)) Ω)⁻¹)) (fun x => ∏ i, r i (x i)) ≤ ENNReal.ofReal δ →
    ∃ A : Fin (n+1) → Set X, (∀ i, MeasurableSet (A i) ∧ μ (A i) ≠ 0 ∧ μ (A i) ≠ ⊤) ∧
      (cubeMeasure μ (n+1)).real (Ω ∆ Set.univ.pi A) ≤ η * (cubeMeasure μ (n+1)).real Ω := by
  let θ := min (1/2) (η/3)
  let m := ((n+1:ℕ):ℝ)
  let κ := θ / (1+3*m)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hm : 1 ≤ m := by dsimp [m]; norm_num
  have hk : 0 < κ := div_pos hθ (by linarith)
  have hkθ : κ ≤ θ := (div_le_iff₀ (by linarith : 0 < 1+3*m)).2 (by nlinarith)
  have hk1 : ENNReal.ofReal κ < 1 := ENNReal.ofReal_lt_one.mpr (hkθ.trans_lt
    ((min_le_left _ _).trans_lt (by norm_num : (1/2:ℝ)<1)))
  refine ⟨κ/2, half_pos hk, ?_⟩
  intro X _ μ _ Ω hΩ h0 ht r hr hn H
  let ν := cubeMeasure μ (n+1)
  let W := Ω.indicator (fun _ => (ν Ω)⁻¹)
  let R := fun x : Fin (n+1) → X => ∏ i, r i (x i)
  have hRW : l1DensityError ν R W < ENNReal.ofReal κ := by
    rw [l1DensityError_comm]
    exact H.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hk).mpr (half_lt_self hk))
  have fibre (i : Fin (n+1)) :=
    select_indicator_fibre μ hΩ r hr hn (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr h0) hRW i
  choose A b hA hb hb' hnear using fibre
  let B := Set.univ.pi A
  let Q := fun i => (A i).indicator (fun _ => (μ (A i))⁻¹)
  have hQm i : Measurable (Q i) := measurable_const.indicator (hA i)
  have hh (i) := normalize_indicator_fibre μ (hA i) (hr i) (hn i) (hb i) (hb' i) hk1 (hnear i)
  have hQn i : (∫⁻ x, Q i x ∂μ) = 1 := by
    rw [show (∫⁻ x, Q i x ∂μ) = (μ (A i))⁻¹ * μ (A i) from lintegral_indicator_const (hA i) _]
    exact ENNReal.inv_mul_cancel (hh i).1 (hh i).2.1
  have hBn : ν B = ∏ i, μ (A i) := Measure.pi_pi (fun _ => μ) A
  have hBm : MeasurableSet B := MeasurableSet.univ_pi hA
  have hBz : ν B ≠ 0 := hBn.trans_ne (Finset.prod_ne_zero_iff.mpr (fun i _ => (hh i).1))
  have hBt : ν B ≠ ⊤ := hBn.trans_ne (ENNReal.prod_ne_top (fun i _ => (hh i).2.1))
  have heq : (fun x : Fin (n+1) → X => ∏ i, Q i (x i)) = B.indicator (fun _ => (ν B)⁻¹) := by
    classical
    funext x
    by_cases h : x ∈ B
    · rw [Set.indicator_of_mem h, hBn]
      have hin : ∀ i, x i ∈ A i := Set.mem_univ_pi.mp h
      simp only [Q, Set.indicator_of_mem (hin _)]
      exact (ENNReal.prod_inv_distrib (fun i _ k _ _ => Or.inl (hh i).1)).symm
    · rw [Set.indicator_of_notMem h]
      obtain ⟨i,hi⟩ : ∃ i, x i ∉ A i := by simpa only [B, Set.mem_univ_pi, not_forall] using h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  have hTensor := l1_product_densities_le μ (n+1) r Q hr hQm hn hQn
  rw [heq] at hTensor
  have hsum : (∑ i, l1DensityError μ (r i) (Q i)) ≤ (n+1 : ℕ) * (3 * ENNReal.ofReal κ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hh i).2.2
  have hdist : l1DensityError ν W (B.indicator (fun _ => (ν B)⁻¹)) ≤ ENNReal.ofReal θ := by
    apply (l1DensityError_triangle ν (measurable_const.indicator hΩ)
      (Finset.measurable_prod _ (fun i _ => (hr i).comp (measurable_pi_apply i)))
      (measurable_const.indicator hBm)).trans
    apply (add_le_add ((l1DensityError_comm ν R W).ge.trans hRW.le) (hTensor.trans hsum)).trans_eq
    have hc : κ + m*(3*κ) = θ := by dsimp [κ]; field_simp
    have H := congrArg ENNReal.ofReal hc
    rw [ENNReal.ofReal_add hk.le (by positivity : 0 ≤ m*(3*κ)),
      ENNReal.ofReal_mul (show 0 ≤ m by linarith), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)] at H
    simpa only [m,ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using H
  refine ⟨A,fun i => ⟨hA i,(hh i).1,(hh i).2.1⟩, ?_⟩
  apply (symmDiff_of_indicator_error ν hΩ hBm h0 ht hBz hBt hθ.le (min_le_left _ _) hdist).trans
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  have H := min_le_right (1/2:ℝ) (η/3)
  dsimp [θ]; linarith only [H]

end LpGowers
