module

public import LpGowers.LogTensorBox
public import LpGowers.BoxTransfer

/-! # The box approximation in the proof of improved log-convexity -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

/-- Under the two adjacent unit normalizations, near equality in ordinary
log-convexity gives a box of mass near one, approximating the autocorrelation
simultaneously in L¹ and squared L². -/
theorem normalized_log_box.{u} (j : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G]
      [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0),
      AEMeasurable f μ → ordinaryGowers μ (j+1) f = 1 → ordinaryGowers μ (j+2+1) f = 1 →
      ENNReal.ofReal (1-δ) ≤ ordinaryGowers μ (j+2) f →
      ∃ A : Fin (j+2) → Set G, (∀ i, MeasurableSet (A i) ∧ μ (A i) ≠ 0 ∧ μ (A i) ≠ ⊤) ∧
        |(cubeMeasure μ (j+2)).real (Set.univ.pi A)-1| ≤ η ∧
        (∫⁻ x, indicatorError (autocorrelation μ (j+2) f) (Set.univ.pi A) x +
          (indicatorError (autocorrelation μ (j+2) f) (Set.univ.pi A) x)^2 ∂cubeMeasure μ (j+2)) ≤
          ENNReal.ofReal η := by
  let κ := η/6
  have hκ : 0<κ := div_pos hη (by norm_num)
  obtain ⟨δ,hδ,hδ1,H⟩ := normalized_log_support.{u} j κ hκ
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf hlow hhigh hmid
  obtain ⟨S,A,hS,hs,hm,hA,hdiff,herr⟩ := H G μ f hf hlow hhigh hmid
  let ν := cubeMeasure μ (j+2)
  let F := autocorrelation μ (j+2) f
  have hF := measurable_autocorrelation_of_aemeasurable μ (j+2) hf
  have hB : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi (fun i => (hA i).1)
  have hB' : ν (Set.univ.pi A) ≠ ⊤ := (Measure.pi_pi (fun _ : Fin (j+2) => μ) A).trans_ne
    (ENNReal.prod_ne_top (fun i _ => (hA i).2.2))
  have ha := (logLower_parameters j).2.2
  have h1 := herr 1 ⟨ha.le,by norm_num⟩
  have h2 := herr 2 ⟨by linarith,le_rfl⟩
  simp only [ENNReal.rpow_one] at h1
  have hb := indicator_error_transfer ν F hF hS hB hs hB' hκ.le hm hdiff h1
    (by simpa only [indicatorError,ENNReal.rpow_two,F] using h2)
  refine ⟨A,hA,hb.1.trans ?_,hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩ <;> dsimp [κ] <;> linarith

end LpGowers
