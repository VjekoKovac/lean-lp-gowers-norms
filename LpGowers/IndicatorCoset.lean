module

public import LpGowers.Normalization
public import LpGowers.PowerTransfer
public import Mathlib.MeasureTheory.Measure.Real

/-! # A quantitative estimate for normalized indicators

Moving the support costs the measure of its symmetric difference multiplied
by the original height. Changing the height on the new support costs the
absolute difference of the two masses divided by the original mass. Taking
a sublinear power gives the estimate in every finite `Lˢ`, `s ≥ 1`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Pointwise symmDiff
namespace LpGowers

/-- `L¹` cost of changing both the support and the height. -/
theorem indicator_distance_one {X : Type*} [MeasurableSpace X] (μ : Measure X) {E C : Set X}
    (hE : MeasurableSet E) (hC : MeasurableSet C) (a b : ℝ≥0) :
    lpDist μ 1 (E.indicator (fun _ => a)) (C.indicator (fun _ => b)) ≤
      (a : ℝ≥0∞) * μ (E ∆ C) + edist a b * μ C := by
  classical
  let f (x : X) := E.indicator (fun _ => a) x
  let g (x : X) := C.indicator (fun _ => a) x
  let h (x : X) := C.indicator (fun _ => b) x
  have hf (x : X) : edist (f x) (g x) = (E ∆ C).indicator (fun _ => (a : ℝ≥0∞)) x := by
    by_cases hx : x ∈ E <;> by_cases hy : x ∈ C <;>
      simp [f,g,Set.mem_symmDiff, hx,hy, edist_dist, NNReal.dist_eq]
  have hg (x : X) : edist (g x) (h x) = C.indicator (fun _ => edist a b) x := by
    by_cases hx : x ∈ C <;> simp [g,h,hx]
  simp only [lpDist,lp,div_one, ENNReal.rpow_one]
  calc
    _ ≤ ∫⁻ x, edist (f x) (g x) + edist (g x) (h x) ∂μ := lintegral_mono (fun x => edist_triangle _ _ _)
    _ = _ := by
      simp_rw [hf,hg]
      rw [lintegral_add_left (measurable_const.indicator (hE.symmDiff hC)),
        lintegral_indicator_const (hE.symmDiff hC), lintegral_indicator_const hC]

/-- For normalized probability densities the height-change cost simplifies to
relative mass change. Both errors are bounded by the same tolerance. -/
theorem normalized_indicators_l1 {X : Type*} [MeasurableSpace X] (μ : Measure X) {E C : Set X}
    (hE : MeasurableSet E) (hC : MeasurableSet C) (hEpos : 0 < μ E) (hEfin : μ E ≠ ⊤)
    (hCpos : 0 < μ C) (hCfin : μ C ≠ ⊤) {η : ℝ}
    (hdiff : μ.real (E ∆ C) ≤ η * μ.real E) (hmass : |μ.real C - μ.real E| ≤ η * μ.real E) :
    lpDist μ 1 (E.indicator (fun _ => (μ E).toNNReal⁻¹))
       (C.indicator (fun _ => (μ C).toNNReal⁻¹)) ≤ ENNReal.ofReal (2 * η) := by
  let a := (μ E).toNNReal⁻¹
  let b := (μ C).toNNReal⁻¹
  have hM : 0 < μ.real E := ENNReal.toReal_pos hEpos.ne' hEfin
  have hN : 0 < μ.real C := ENNReal.toReal_pos hCpos.ne' hCfin
  have hdiffFin : μ (E ∆ C) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hEfin,hCfin⟩)
    ((measure_mono Set.symmDiff_subset_union).trans (measure_union_le _ _))
  have hd : edist a b = ENNReal.ofReal |(μ.real E)⁻¹ - (μ.real C)⁻¹| := by rw [edist_dist,NNReal.dist_eq]; rfl
  have ha : (a : ℝ≥0∞) = ENNReal.ofReal (μ.real E)⁻¹ := by
    change (a : ℝ≥0∞) = ENNReal.ofReal (a : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  have hsum := indicator_distance_one μ hE hC a b
  apply hsum.trans
  rw [ha, hd, ← ENNReal.ofReal_toReal hdiffFin, ← ENNReal.ofReal_toReal hCfin,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le), ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (inv_nonneg.mpr hM.le) ENNReal.toReal_nonneg)
      (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  change (μ.real E)⁻¹ * μ.real (E ∆ C) + |(μ.real E)⁻¹ - (μ.real C)⁻¹| * μ.real C ≤ _
  have hid : |(μ.real E)⁻¹ - (μ.real C)⁻¹| * μ.real C = |μ.real C-μ.real E|/(μ.real E) := by
    rw [show (μ.real E)⁻¹ - (μ.real C)⁻¹ = (μ.real C-μ.real E)/((μ.real E)*(μ.real C)) by field_simp, abs_div,
      abs_of_pos (mul_pos hM hN)]
    field_simp
  rw [hid, inv_mul_eq_div]
  linarith [ (div_le_iff₀ hM).mpr hdiff, (div_le_iff₀ hM).mpr hmass ]

/-- Relative errors in the support and its measure yield an arbitrarily small
distance to the normalized coset profile. The threshold is uniform in the group,
the Haar measure, the set and the coset. -/
theorem normalized_indicator_close_coset (s : ℝ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
      (E : Set G) (H : AddSubgroup G) (x₀ : G),
      MeasurableSet E → 0 < μ E → μ E ≠ ⊤ → IsCompact (H : Set G) → IsOpen (H : Set G) →
      μ.real (E ∆ {x | x-x₀ ∈ H}) ≤ η * μ.real E →
      |μ.real (H : Set G) - μ.real E| ≤ η * μ.real E →
      lpDist μ s (E.indicator (fun _ => (μ E).toNNReal ^ (-(1/s))))
        (cosetProfile μ s 1 H x₀) ≤ ENNReal.ofReal ε := by
  classical
  refine ⟨ε^s/2, half_pos (Real.rpow_pos_of_pos hε s), ?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ E H x₀ hE hEpos hEfin hc ho hd hm
  let C : Set G := {x | x-x₀ ∈ H}
  have hC : MeasurableSet C := (measurable_id.sub measurable_const) ho.measurableSet
  have hmC : μ C = μ (H : Set G) := by
    change μ ((fun x => x-x₀) ⁻¹' (H : Set G)) = _
    simpa only [sub_eq_add_neg] using measure_preimage_add_right μ (-x₀) (H : Set G)
  have hrC : μ.real C = μ.real (H : Set G) := congrArg ENNReal.toReal hmC
  have hCpos : 0 < μ C := hmC.symm ▸ ho.measure_pos μ ⟨0,H.zero_mem⟩
  have hCfin : μ C ≠ ⊤ := hmC.symm ▸ hc.measure_lt_top.ne
  have hl := normalized_indicators_l1 μ hE hC hEpos hEfin hCpos hCfin hd (hrC.symm ▸ hm)
  let u := E.indicator (fun _ => (μ E).toNNReal⁻¹)
  let v := C.indicator (fun _ => (μ C).toNNReal⁻¹)
  have hs₀ : 0 < s := zero_lt_one.trans_le hs
  have hg : 0 < 1/s := one_div_pos.mpr hs₀
  have hroot : 1 / (1/s) = s := by simp
  have hu : (fun x => u x ^ (1/s)) = E.indicator (fun _ => (μ E).toNNReal ^ (-(1/s))) := by
    funext x
    by_cases hx : x ∈ E <;> simp [u,hx,NNReal.rpow_neg,NNReal.inv_rpow, hs₀.ne']
  have hv : v = cosetProfile μ 1 1 H x₀ := by
    funext x
    by_cases hx : x ∈ C
    · have hx' : x-x₀ ∈ H := hx
      simp [v, hx, cosetProfile, hx', hmC, one_div]
    · have hx' : x-x₀ ∉ H := hx
      simp [v, hx, cosetProfile, hx']
  have hpow := lpDist_rpow_sublinear μ (r := 1) (by norm_num) hg ((div_le_one hs₀).mpr hs) u v
  rw [hu, hv, cosetProfile_unit_rpow μ 1 (1/s) (by norm_num) hg H x₀ hc ho, hroot] at hpow
  change lpDist μ 1 u v ≤ _ at hl
  rw [hv] at hl
  apply hpow.trans ((ENNReal.rpow_le_rpow hl hg.le).trans_eq ?_)
  rw [show 2 * (ε ^ s / 2) = ε ^ s by ring,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.le _) hg.le,
    ← Real.rpow_mul hε.le, mul_one_div_cancel hs₀.ne', Real.rpow_one]

end LpGowers
