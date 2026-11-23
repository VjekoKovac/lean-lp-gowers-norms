module

public import LpGowers.BoxSlices

/-! Uniform choice of slice tolerance, independent of the LCA group. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

private theorem choose_slice_tolerance (k : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ η ∧ t/η + 1/(1+η) < (1-t)^k := by
  let F := fun t : ℝ => (1-t)^k - (t/η + 1/(1+η))
  have hc : ContinuousAt F 0 := by dsimp [F]; fun_prop
  have h1 : 1/(1+η) < 1 := by
    rw [div_lt_one (by linarith : 0 < 1+η)]; linarith
  have h0 : 0 < F 0 := by simpa [F] using sub_pos.mpr h1
  obtain ⟨s,hs,H⟩ := Metric.continuousAt_iff.mp hc (F 0) h0
  let t := min (s/2) η
  have ht : 0 < t := lt_min (by positivity) hη
  have hts : t < s := lt_of_le_of_lt (min_le_left ..) (by linarith)
  have h := H (show dist t 0 < s by simpa [Real.dist_eq, abs_of_pos ht] using hts)
  rw [Real.dist_eq] at h
  have hh := (abs_lt.mp h).1
  exact ⟨t,ht,min_le_right ..,by dsimp [F] at hh; linarith⟩

/-- For a near-unit box approximating the full autocorrelation, freeze a
common set of increments so that the resulting degree-two input satisfies
both error and mass bounds. -/
theorem good_slice_of_near_unit_sides (k : ℕ) {η : ℝ} (hη : 0 < η) (hη' : η < 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ η ∧ ∀ {G : Type*} [AddCommGroup G] [MeasurableSpace G]
      [MeasurableAdd₂ G] (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] {f : G → ℝ≥0},
      AEMeasurable f μ → ordinaryGowers μ (k+1) f = 1 →
      ∀ A : Fin (k+2) → Set G, (∀ i, MeasurableSet (A i)) →
      (∀ i, ENNReal.ofReal (1-τ) ≤ μ (A i)) → boxError μ (k+2) f A ≤ ENNReal.ofReal τ →
      ∃ z : Fin k → G, boxError μ 2 (sliceInput k f z) ![A 0,A 1] ≤ ENNReal.ofReal η ∧
        (∫⁻ x, (sliceInput k f z x : ℝ≥0∞) ∂μ)^2 ≤ ENNReal.ofReal (1+η) := by
  obtain ⟨t,ht,htη,H⟩ := choose_slice_tolerance k η hη hη'
  refine ⟨t,ht,htη,?_⟩
  intro G _ _ _ μ _ _ f hf hprev A hA hside hbox
  have ht1 : 0 ≤ 1-t := by linarith
  have hb : 0 < 1+η := by linarith
  have H' := (ENNReal.ofReal_lt_ofReal_iff (pow_pos (by linarith : 0 < 1-t) k)).mpr H
  rw [ENNReal.ofReal_add (div_nonneg ht.le hη.le) (by positivity),
    ENNReal.ofReal_div_of_pos hη, ENNReal.ofReal_div_of_pos hb,
    ENNReal.ofReal_one, ENNReal.ofReal_pow ht1] at H'
  have hm : (ENNReal.ofReal (1-t))^k ≤
      cubeMeasure μ k (Set.univ.pi (fun i : Fin k => A i.succ.succ)) := by
    rw [cubeMeasure, Measure.pi_pi]
    simpa using Finset.prod_le_prod (s := Finset.univ) (fun (i : Fin k) _ => hside i.succ.succ)
  have hbound := lt_of_le_of_lt (add_le_add_left
    (show boxError μ (k+2) f A / ENNReal.ofReal η ≤ ENNReal.ofReal t / ENNReal.ofReal η by gcongr)
    (1 / ENNReal.ofReal (1+η))) (H'.trans_le hm)
  obtain ⟨z,hz,hz'⟩ := select_box_slice μ hf k A hA (ENNReal.ofReal_pos.mpr hη).ne'
    ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top hprev hbound
  exact ⟨z,hz.le,hz'.le⟩

end LpGowers
