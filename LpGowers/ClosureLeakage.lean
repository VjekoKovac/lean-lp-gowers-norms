module

public import LpGowers.DiagonalEstimate

/-! # From concentration on a square to near closure under addition

This is the last step of the two-dimensional argument leading to the near-closure estimate.
The error for the square indicator is measured in `L¹`. Inside the candidate
set only the squared deficit of the first correlation below one is needed.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

/-- For a density concentrated on a measurable set of mass close to its total
mass, bound the mass off the set by the squared deficit on the set. -/
theorem tail_from_deficit {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {K : Set X} (hK : MeasurableSet K) (hfin : μ K ≠ ⊤)
    {v : X → ℝ≥0∞} (hv : Measurable v) :
    (∫⁻ x in Kᶜ, v x ∂μ) ≤ (∫⁻ x, v x ∂μ) + (μ K)^(1/2:ℝ) *
      (∫⁻ x in K, (1 - v x)^2 ∂μ)^(1/2:ℝ) - μ K := by
  let b (x : X) := 1 - v x
  have hb : Measurable b := measurable_const.sub hv
  have h0 : ∫⁻ x in K, b x ∂μ ≤ (μ K)^(1/2:ℝ) * (∫⁻ x in K, (b x)^2 ∂μ)^(1/2:ℝ) := by
    have htwo : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict K) htwo
      (f := fun _ : X => (1:ℝ≥0∞)) (g := b) measurable_const.aemeasurable hb.aemeasurable
    simpa only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.rpow_two,one_pow] using h
  have hmass : μ K ≤ (∫⁻ x in K, v x ∂μ) + ∫⁻ x in K, b x ∂μ := by
    rw [← lintegral_add_left hv]
    calc
      _ = ∫⁻ _ in K, (1:ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := lintegral_mono (fun x => le_add_tsub (a := 1) (b := v x))
  apply ENNReal.le_sub_of_add_le_left hfin
  calc
    _ ≤ ((∫⁻ x in K, v x ∂μ) + (∫⁻ x in K, b x ∂μ)) + ∫⁻ x in Kᶜ, v x ∂μ :=
      add_le_add_left hmass _
    _ = (∫⁻ x, v x ∂μ) + ∫⁻ x in K, b x ∂μ := by rw [add_right_comm, lintegral_add_compl _ hK]
    _ ≤ _ := add_le_add_right h0 _

/-- The measure of pairs in `K × K` whose sum leaves `K` is bounded by the
error of the square model plus the diagonal leakage of the true density. -/
theorem measure_bad_pairs_le {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {K : Set G} (hK : MeasurableSet K) :
    μ.prod μ {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K} ≤
      l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
        (fun h => ((K ×ˢ K).indicator (1 : G × G → ℝ≥0∞)) (h 0,h 1)) +
      (∫⁻ s in Kᶜ, pairCorrelation μ (liftNN f) (liftNN f) s ∂μ)^(1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  classical
  let B : Set (G × G) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K}
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  have hB : MeasurableSet B := (measurable_fst hK).inter
    ((measurable_snd hK).inter ((measurable_fst.add measurable_snd) hK.compl))
  let u := autocorrelation μ 2 f
  let w (h : Fin 2 → G) := ((K ×ˢ K).indicator (1 : G × G → ℝ≥0∞)) (h 0,h 1)
  let D (h : Fin 2 → G) := (u h - w h) + (w h - u h)
  have hu : Measurable u := measurable_autocorrelation_of_aemeasurable μ 2 hf
  have hw : Measurable w := (measurable_const.indicator (hK.prod hK)).comp
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have hD : Measurable D := (hu.sub hw).add (hw.sub hu)
  let A (h : Fin 2 → G) := Kᶜ.indicator (1 : G → ℝ≥0∞) (h 0+h 1) * u h
  have hm : μ.prod μ B = ∫⁻ h, (e ⁻¹' B).indicator (1 : (Fin 2 → G) → ℝ≥0∞) h ∂cubeMeasure μ 2 := by
    simp [lintegral_indicator (e.measurable hB), he.measure_preimage hB.nullMeasurableSet]
  calc
    _ = _ := hm
    _ ≤ ∫⁻ h, D h+A h ∂cubeMeasure μ 2 := by
      apply lintegral_mono; intro h
      by_cases hz : e h ∈ B
      · have hz₀ := hz
        obtain ⟨h1,h2,hs⟩ : h 0 ∈ K ∧ h 1 ∈ K ∧ h 0+h 1 ∉ K := hz₀
        have hle : 1 ≤ u h + (1-u h) := le_add_tsub
        simp only [Set.indicator_of_mem (show h ∈ e ⁻¹' B from hz), Pi.one_apply,
          A,D,w, Set.indicator_of_mem (show (h 0,h 1) ∈ K ×ˢ K from ⟨h1,h2⟩),
          Set.indicator_of_mem (show h 0+h 1 ∈ Kᶜ from hs), one_mul]
        apply hle.trans
        rw [add_comm (u h) (1-u h)]
        exact add_le_add_left (le_add_left (le_refl _) ) _
      · simp [Set.indicator_of_notMem (show h ∉ e ⁻¹' B from hz)]
    _ ≤ _ := by
      rw [lintegral_add_left hD]
      exact add_le_add_right (diagonal_leakage μ hf hK.compl) _

/-- The total mass of the first autocorrelation. The marginal formula in
one increment gives exactly the square of the original mass. -/
theorem pairCorrelation_self_mass {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    (∫⁻ x, pairCorrelation μ (liftNN f) (liftNN f) x ∂μ) = (∫⁻ x, liftNN f x ∂μ)^2 := by
  convert! autocorrelation_marginal μ hf 0 0 (fun i => Fin.elim0 i) using 1

/-- A direct quantitative form of the two-dimensional near-closure step in
§6. The bounds are useful when the input mass and the set's measure are
close to one and the first and second correlations approximate their set models. -/
theorem bad_pairs_from_square {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {K : Set G} (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) :
    let v := pairCorrelation μ (liftNN f) (liftNN f)
    μ.prod μ {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K} ≤
      l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
        (fun h => ((K ×ˢ K).indicator (1 : G × G → ℝ≥0∞)) (h 0,h 1)) +
      ((∫⁻ x, liftNN f x ∂μ)^2 + (μ K)^(1/2:ℝ) * (∫⁻ x in K, (1-v x)^2 ∂μ)^(1/2:ℝ) - μ K)^(1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  let v := pairCorrelation μ (liftNN f) (liftNN f)
  have hv : Measurable v := (measurable_autocorrelation_of_aemeasurable μ 1 hf).comp
    (show Measurable (fun t : G => fun _ : Fin 1 => t) from measurable_pi_iff.mpr fun _ => measurable_id)
  have ht := tail_from_deficit μ hK hfin hv
  change (∫⁻ x in Kᶜ, v x ∂μ) ≤ (∫⁻ x, pairCorrelation μ (liftNN f) (liftNN f) x ∂μ) + _ - μ K at ht
  rw [pairCorrelation_self_mass μ hf] at ht
  refine (measure_bad_pairs_le μ hf hK).trans ?_
  exact add_le_add_right (mul_le_mul_left (mul_le_mul_left
    (ENNReal.rpow_le_rpow ht (by norm_num : (0:ℝ) ≤ 1/2)) _) _) _

end LpGowers
