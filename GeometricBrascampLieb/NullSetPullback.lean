module

public import GeometricBrascampLieb.Geometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

@[expose] public section

/-! # Pulling back null sets under the geometric maps -/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F)

/-- A geometric map pulls back every null set to a null set, even with nontrivial kernel. -/
theorem map_quasiMeasurePreserving (i : ι) :
    QuasiMeasurePreserving (D.map i) (volume : Measure E) (volume : Measure (F i)) := by
  refine ⟨(D.map i).continuous.measurable.aemeasurable, ?_⟩
  obtain ⟨c, _, hc⟩ := (D.map i).toLinearMap.exists_map_addHaar_eq_smul_addHaar
    (volume : Measure E) (volume : Measure (F i)) (D.map_surjective i)
  change Measure.map (D.map i).toLinearMap volume ≪ volume
  rw [hc]
  exact Measure.smul_absolutelyContinuous

end GeometricBrascampLieb.Datum
