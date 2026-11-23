module

public import LpGowers.InverseDifference
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Tactic

/-! # From additive closure in measure to a compact open subgroup

A finite positive-mass measurable set on which addition fails on fewer than
one hundredth of pairs forces a compact open subgroup. The proof uses the
overlap function and the small-difference-set lemma of Eisner and Tao.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace LpGowers

/-- A common lower bound on sections bounds the product measure below. -/
lemma fiber_mass_bound {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    (E : Set (G × G)) (hE : MeasurableSet E) (hfin : (μ.prod μ) E ≠ ⊤)
    (B : Set G) (hB : MeasurableSet B) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ x ∈ B, c ≤ μ.real (Prod.mk x ⁻¹' E)) :
    c * μ.real B ≤ (μ.prod μ).real E := by
  have hh : ENNReal.ofReal c * μ B ≤ (μ.prod μ) E := by
    rw [Measure.prod_apply hE]
    calc
      _ = ∫⁻ x in B, ENNReal.ofReal c ∂μ := (setLIntegral_const ..).symm
      _ ≤ ∫⁻ x in B, μ (Prod.mk x ⁻¹' E) ∂μ :=
        setLIntegral_mono' hB fun x hx => ENNReal.ofReal_le_of_le_toReal (hf x hx)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    using ENNReal.toReal_mono hfin hh

/-- The rejection probability for an independent pair of uniform points of
`K` is less than one percent. The argument also applies to noncompact `K`
of positive finite Haar measure. -/
theorem compact_open_subgroup_of_small_additive_leakage
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (K : Set G) (hK : MeasurableSet K) (hpos : 0 < μ K) (hfin : μ K ≠ ⊤)
    (hleak : (μ.prod μ).real {z : G × G | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K} <
      (μ.real K)^2 / 100) :
    ∃ H : AddSubgroup G, IsCompact (H : Set G) ∧ IsOpen (H : Set G) := by
  classical
  let m := μ.real K
  have hm : 0 < m := ENNReal.toReal_pos hpos.ne' hfin
  let T := fun a : G => fun S : Set G => (fun z => z+a) ⁻¹' S
  have hT (a : G) (S : Set G) : μ.real (T a S) = μ.real S := by
    simp only [measureReal_def,T,measure_preimage_add_right]
  have mT (a : G) : MeasurableSet (T a K) := (measurable_id.add_const a) hK
  let P : Set (G × G) := {z | z.2 ∈ K ∧ z.2+z.1 ∈ K}
  have hP : MeasurableSet P := (measurable_snd hK).inter ((measurable_snd.add measurable_fst) hK)
  have pMass : (μ.prod μ) P = μ K * μ K :=
    ((measurePreserving_prod_add_swap μ μ).measure_preimage (hK.prod hK).nullMeasurableSet).trans
      (Measure.prod_prod K K)
  let R := fun a : G => μ.real (K ∩ T a K)
  have measR : Measurable R := (measurable_measure_prodMk_left (ν := μ) hP).ennreal_toReal
  let S := K ∩ {x | 9*m/10 < R x}
  have hS : MeasurableSet S := hK.inter (measurableSet_lt measurable_const measR)
  have sK : S ⊆ K := inter_subset_left
  have sf : μ S ≠ ⊤ := measure_ne_top_of_subset sK hfin
  let L : Set (G × G) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K}
  have hL : MeasurableSet L := (measurable_fst hK).inter
    ((measurable_snd hK).inter (((measurable_fst.add measurable_snd) hK).compl))
  have hLf : (μ.prod μ) L ≠ ⊤ := by
    have sub : L ⊆ K ×ˢ K := fun z hz => ⟨hz.1,hz.2.1⟩
    apply measure_ne_top_of_subset sub
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hfin hfin
  have small := fiber_mass_bound μ L hL hLf (K \ S) (hK.diff hS) (m/10) (by positivity)
    (by
      intro x hx
      have hxK : x ∈ K := hx.1
      have hb : R x ≤ 9*m/10 := le_of_not_gt fun h => hx.2 ⟨hxK,h⟩
      have es : Prod.mk x ⁻¹' L = K \ T x K := by
        ext z
        simp [L,T,hxK,add_comm x]
      rw [es]
      have hi := measureReal_sdiff_add_inter (μ := μ) (s := K) (mT x) hfin
      change _ + R x = m at hi
      linarith)
  have sMass : 9*m/10 < μ.real S := by
    change (μ.prod μ).real L < m^2/100 at hleak
    rw [measureReal_sdiff sK hS hfin] at small
    change m/10 * (m-μ.real S) ≤ _ at small
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h hm.le]
  have cutoff : ENNReal.ofReal (17*m/20) < μ S :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) sf).2 (by change _ < μ.real S; linarith)
  obtain ⟨A,hAS,hAc,hAm⟩ := hS.exists_lt_isCompact_of_ne_top sf cutoff
  have hAf := hAc.measure_lt_top (μ := μ)
  have hAr : 17*m/20 < μ.real A :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hAf.ne).mp hAm
  have hAp : 0 < μ A := lt_of_le_of_lt bot_le hAm
  let D := A - A
  have dc : IsCompact D := by
    have him : (fun z : G × G => z.1-z.2) '' (A ×ˢ A) = D := by
      ext t
      constructor
      · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
        exact ⟨a,ha,b,hb,rfl⟩
      · rintro ⟨a,ha,b,hb,rfl⟩
        exact ⟨(a,b),⟨ha,hb⟩,rfl⟩
    rw [← him]
    exact (hAc.prod hAc).image continuous_sub
  have fiber (t : G) (ht : t ∈ D) : 4*m/5 ≤ R t := by
    obtain ⟨a,ha,b,hb,rfl⟩ := ht
    let X := K ∩ T a K
    let Y := K ∩ T b K
    have hx : 9*m/10 < μ.real X := (hAS ha).2
    have hy : 9*m/10 < μ.real Y := (hAS hb).2
    have hu : μ.real (X ∪ Y) ≤ m :=
      measureReal_mono (union_subset inter_subset_left inter_subset_left) hfin
    have hxy := measureReal_union_add_inter (μ := μ) (s := X) (t := Y) (hK.inter (mT b))
      (measure_ne_top_of_subset inter_subset_left hfin) (measure_ne_top_of_subset inter_subset_left hfin)
    have htr : T b (K ∩ T (a-b) K) = T b K ∩ T a K := by
      ext z
      change (z+b ∈ K ∧ z+b+(a-b) ∈ K) ↔ (z+b ∈ K ∧ z+a ∈ K)
      rw [show z+b+(a-b)=z+a by abel]
    have hsub : X ∩ Y ⊆ T b K ∩ T a K := fun z hz => ⟨hz.2.2,hz.1.2⟩
    have hTf : μ (T b K) ≠ ⊤ := by simpa only [T, measure_preimage_add_right] using hfin
    have hbound := measureReal_mono (μ := μ) hsub (measure_ne_top_of_subset inter_subset_left hTf)
    rw [← htr,hT] at hbound
    change μ.real (X ∩ Y) ≤ R (a-b) at hbound
    linarith
  have hPf : (μ.prod μ) P ≠ ⊤ := pMass ▸ ENNReal.mul_ne_top hfin hfin
  have upper := fiber_mass_bound μ P hP hPf D dc.isClosed.measurableSet (4*m/5)
    (by positivity) fiber
  have hPm : (μ.prod μ).real P = m^2 := by
    rw [measureReal_def,pMass,ENNReal.toReal_mul,pow_two]
    rfl
  rw [hPm] at upper
  have hD : μ.real D < 3/2 * μ.real A := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h hm.le, mul_lt_mul_of_pos_left hAr hm]
  obtain ⟨H,_,hc,ho⟩ := compact_open_subgroup_of_small_difference μ A hAc hAp hD
  exact ⟨H,hc,ho⟩

end LpGowers
