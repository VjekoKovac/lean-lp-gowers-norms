module

public import LpGowers.BoxErrorDefs
public import LpGowers.HigherSlice

/-! Disintegrating the combined first and second power errors of a box
approximation. Freezing all but two coordinates selects a single input
satisfying the autocorrelation and mass estimates simultaneously. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

private theorem boxfun_meas {X : Type*} [MeasurableSpace X] {m : ℕ}
    (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (Set.univ.pi A) := MeasurableSet.pi Set.countable_univ (fun i _ => hA i)

private theorem lintegral_two {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    {F : (Fin 2 → G) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ h, F h ∂cubeMeasure μ 2) = ∫⁻ v, ∫⁻ u, F ![u,v] ∂μ ∂μ := by
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  calc
    _ = ∫⁻ z, F (e.symm z) ∂μ.prod μ := ((he.symm e).lintegral_comp hF).symm
    _ = _ := lintegral_prod_symm' (fun z => F (e.symm z)) (hF.comp e.symm.measurable)

/-- Restricting the frozen variables to the remaining sides of the box can
only decrease the integral of the nonnegative slice errors. -/
theorem lintegral_slice_boxError {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (k : ℕ) (A : Fin (k+2) → Set G) (hA : ∀ i, MeasurableSet (A i)) :
    let D := Set.univ.pi (fun i : Fin k => A i.succ.succ)
    (∫⁻ z in D, boxError μ 2 (sliceInput k f z) ![A 0,A 1] ∂cubeMeasure μ k) ≤ boxError μ (k+2) f A := by
  intro D
  let I := (Set.univ.pi A).indicator (fun _ => (1 : ℝ≥0∞))
  let F := fun h => boxErrorAt (autocorrelation μ (k+2) f h) (I h)
  have hI : Measurable I := measurable_one.indicator (boxfun_meas A hA)
  have hF : Measurable F := by
    dsimp [F,boxErrorAt]; have h := measurable_autocorrelation_of_aemeasurable μ (k+2) hf; fun_prop
  have hg (z : Fin k → G) := sliceInput_aemeasurable μ hf k z
  let B : Fin 2 → Set G := ![A 0,A 1]
  have hB : ∀ i, MeasurableSet (B i) := fun i => by fin_cases i <;> simp [B,hA]
  let J := (Set.univ.pi B).indicator (fun _ => (1 : ℝ≥0∞))
  have hJ : Measurable J := measurable_one.indicator (boxfun_meas B hB)
  have hD : MeasurableSet D := boxfun_meas _ (fun i => hA _)
  change _ ≤ ∫⁻ h, F h ∂cubeMeasure μ (k+2)
  rw [lintegral_two_free μ k hF]
  apply (setLIntegral_mono_ae' hD ?_).trans (setLIntegral_le_lintegral _ _)
  filter_upwards with z hz
  have eqI (u v : G) : I (Fin.cons u (Fin.cons v z)) = J ![u,v] := by
    have hz' : ∀ i, z i ∈ A i.succ.succ := Set.mem_univ_pi.mp hz
    have hiff : Fin.cons u (Fin.cons v z) ∈ Set.univ.pi A ↔ ![u,v] ∈ Set.univ.pi B := by
      simp [Fin.forall_fin_succ, hz', B]
    by_cases hzB : ![u,v] ∈ Set.univ.pi B
    · simp [I,J,hzB,hiff.mpr hzB]
    · simp [I,J,hzB,mt hiff.mp hzB]
  let M := fun h => boxErrorAt (autocorrelation μ 2 (sliceInput k f z) h) (J h)
  have hM : Measurable M := by
    dsimp [M,boxErrorAt]; have h := measurable_autocorrelation_of_aemeasurable μ 2 (hg z); fun_prop
  change (∫⁻ h, M h ∂cubeMeasure μ 2) ≤ _
  rw [lintegral_two μ hM]
  apply lintegral_mono; intro v
  apply lintegral_mono; intro u
  exact le_of_eq (by simp only [M,F,eqI,(slice_autocorrelations μ f k z u v).2.2])

private theorem consMap_meas {G : Type*} [MeasurableSpace G] (k : ℕ) :
    Measurable (fun t : G × (Fin k → G) => Fin.cons t.1 t.2 : _ → Fin (k+1) → G) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => G) 0).symm.measurable
  convert h using 1
  funext t
  exact (Fin.insertNth_zero' _ _).symm

private theorem measurable_slice_boxError {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) (k : ℕ) (B : Fin 2 → Set G) (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (fun z => boxError μ 2 (sliceInput k f z) B) := by
  let J := (Set.univ.pi B).indicator (fun _ => (1 : ℝ≥0∞))
  let V := fun h : Fin (k+2) → G => ![h 0,h 1]
  have hV : Measurable V := measurable_pi_iff.mpr (fun i => by fin_cases i <;> exact measurable_pi_apply _)
  have hJ : Measurable J := measurable_one.indicator (boxfun_meas B hB)
  let F := fun h => boxErrorAt (autocorrelation μ (k+2) f h) (J (V h))
  have hF : Measurable F := by
    dsimp [F,boxErrorAt]
    have h := measurable_autocorrelation_of_aemeasurable μ (k+2) hf
    have hj := hJ.comp hV
    fun_prop
  have hu := Measurable.lintegral_prod_left' (μ := μ) (hF.comp (consMap_meas (k+1)))
  have hv := Measurable.lintegral_prod_left' (μ := μ) (hu.comp (consMap_meas k))
  convert hv using 1
  funext z
  let M := fun h => boxErrorAt (autocorrelation μ 2 (sliceInput k f z) h) (J h)
  have hM : Measurable M := by
    dsimp [M,boxErrorAt]
    have h := measurable_autocorrelation_of_aemeasurable μ 2 (sliceInput_aemeasurable μ hf k z)
    fun_prop
  change (∫⁻ h, M h ∂cubeMeasure μ 2) = _
  rw [lintegral_two μ hM]
  apply lintegral_congr; intro v
  apply lintegral_congr; intro u
  simp [F,M,V,(slice_autocorrelations μ f k z u v).2.2]

/-- Exact sufficient bounds for choosing a good slice. The lower-order
unit norm controls the squared mass of the slice input by averaging. -/
theorem select_box_slice {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (k : ℕ) (A : Fin (k+2) → Set G) (hA : ∀ i, MeasurableSet (A i)) {a b : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ⊤) (hb : b ≠ 0) (hb' : b ≠ ⊤)
    (hprev : ordinaryGowers μ (k+1) f = 1)
    (hbound : boxError μ (k+2) f A / a + 1/b <
      cubeMeasure μ k (Set.univ.pi fun i : Fin k => A i.succ.succ)) :
    ∃ z : Fin k → G, boxError μ 2 (sliceInput k f z) ![A 0,A 1] < a ∧
      (∫⁻ x, (sliceInput k f z x : ℝ≥0∞) ∂μ)^2 < b := by
  let D := Set.univ.pi (fun i : Fin k => A i.succ.succ)
  let M := fun z => (autocorrelation μ k f z)^2
  let L := fun z => boxError μ 2 (sliceInput k f z) ![A 0,A 1]
  have hL : Measurable L := measurable_slice_boxError μ hf k _ (fun i => by fin_cases i <;> simp [hA])
  have hm : (∫⁻ z, M z ∂cubeMeasure μ k) = 1 := by
    have hh : lp (cubeMeasure μ (k+1)) 1 (autocorrelation μ (k+1) f) = 1 := by
      have hh := congrArg (fun t : ℝ≥0∞ => t ^ ((2:ℝ)^(k+1))) hprev
      simpa only [ordinaryGowers,gowers,← ENNReal.rpow_mul,one_div_mul_cancel (by positivity : (2:ℝ)^(k+1) ≠ 0),
        ENNReal.rpow_one, ENNReal.one_rpow] using hh
    rw [← lintegral_autocorrelation_succ μ hf k]
    simpa [lp] using hh
  have hl := lintegral_slice_boxError μ hf k A hA
  have hm' : (∫⁻ z in D, M z ∂cubeMeasure μ k) ≤ 1 := (setLIntegral_le_lintegral _ _).trans_eq hm
  have hsmall : (∫⁻ z in D, L z ∂cubeMeasure μ k)/a +
      (∫⁻ z in D, M z ∂cubeMeasure μ k)/b < cubeMeasure μ k D :=
    lt_of_le_of_lt (add_le_add (show (∫⁻ z in D, L z ∂cubeMeasure μ k)/a ≤ boxError μ (k+2) f A/a by gcongr)
      (show (∫⁻ z in D, M z ∂cubeMeasure μ k)/b ≤ 1/b by gcongr)) hbound
  obtain ⟨z,_,hlz,hmz⟩ := exists_good_slice (cubeMeasure μ k) D ha ha' hb hb' hL hsmall
    (boxfun_meas _ (fun i => hA _))
  refine ⟨z,hlz,?_⟩
  simpa only [coe_sliceInput, M, autocorrelation] using hmz

end LpGowers
