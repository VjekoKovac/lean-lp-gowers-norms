module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Tactic.Linarith

/-! # The small-difference lemma in the ordinary inverse theorem

This is the measure argument in Eisner–Tao, arXiv:1012.3509, Lemma 5.5.
The argument works in a second-countable locally compact abelian group.
Steinhaus's theorem supplies the openness of the subgroup. -/

@[expose] public section
open MeasureTheory Set
open scoped Pointwise ENNReal Topology
noncomputable section
namespace LpGowers

/-- If the difference set of a positive-mass compact set has measure
strictly below three halves of its measure, it is a compact open subgroup.
Both measures in the inequality are finite by compactness. -/
theorem compact_open_subgroup_of_small_difference
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (K : Set G) (hc : IsCompact K) (hm : 0 < μ K)
    (hs : μ.real (K-K) < (3/2 : ℝ) * μ.real K) :
    ∃ H : AddSubgroup G, (H : Set G) = K-K ∧ IsCompact (H : Set G) ∧ IsOpen (H : Set G) := by
  let D := K - K
  let T := fun (a : G) (s : Set G) => (fun x => x+a) ⁻¹' s
  have hD : IsCompact D := by
    change IsCompact (K-K)
    have him : (fun z : G × G => z.1-z.2) '' (K ×ˢ K) = K-K := by
      ext x
      constructor
      · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
        exact ⟨a,ha,b,hb,rfl⟩
      · rintro ⟨a,ha,b,hb,rfl⟩
        exact ⟨(a,b),⟨ha,hb⟩,rfl⟩
    rw [← him]
    exact (hc.prod hc).image continuous_sub
  have hfin : μ K ≠ ⊤ := hc.measure_lt_top.ne
  have hmea : MeasurableSet K := hc.isClosed.measurableSet
  have hT (a : G) (s : Set G) : μ (T a s) = μ s := measure_preimage_add_right _ _ _
  have hTr (a : G) (s : Set G) : μ.real (T a s) = μ.real s := by
    change (μ (T a s)).toReal = (μ s).toReal
    rw [hT]
  have mT (a : G) : MeasurableSet (T a K) := (measurable_id.add_const a) hmea
  have subT {a : G} (ha : a ∈ K) : T a K ⊆ D := by
    intro x hx
    exact ⟨x+a,hx,a,ha,add_sub_cancel_right ..⟩
  have hover (a : G) (ha : a ∈ D) : μ.real K / 2 < μ.real (K ∩ T a K) := by
    obtain ⟨u,hu,v,hv,rfl⟩ := ha
    have htr : T v (K ∩ T (u-v) K) = T v K ∩ T u K := by
      ext x
      change (x+v ∈ K ∧ x+v+(u-v) ∈ K) ↔ (x+v ∈ K ∧ x+u ∈ K)
      rw [show x+v+(u-v) = x+u by abel]
    have hinc := measureReal_union_add_inter (μ := μ) (s := T v K) (mT u)
      (by rw [hT]; exact hfin) (by rw [hT]; exact hfin)
    rw [← htr, hTr, hTr, hTr] at hinc
    have hun : μ.real (T v K ∪ T u K) ≤ μ.real D :=
      measureReal_mono (union_subset (subT hv) (subT hu)) hD.measure_lt_top.ne
    change μ.real D < _ at hs
    linarith
  have hsub (a : G) (ha : a ∈ D) (b : G) (hb : b ∈ D) : a-b ∈ D := by
    let A := K ∩ T a K
    let B := K ∩ T b K
    have hfA : μ A ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hc.measure_lt_top).ne
    have hfB : μ B ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt hc.measure_lt_top).ne
    have hinc := measureReal_union_add_inter (μ := μ) (s := A) (t := B) (hmea.inter (mT b)) hfA hfB
    have hU : μ.real (A ∪ B) ≤ μ.real K :=
      measureReal_mono (union_subset inter_subset_left inter_subset_left) hfin
    have hA : μ.real K / 2 < μ.real A := hover _ ha
    have hB : μ.real K / 2 < μ.real B := hover _ hb
    have hn : (A ∩ B).Nonempty := by
      by_contra! h
      have hz : μ.real (A ∩ B) = 0 := by simp [h]
      linarith
    obtain ⟨z,hzA,hzB⟩ := hn
    exact ⟨z+a,hzA.2,z+b,hzB.2,by abel⟩
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hm.ne'
  have h0 : (0 : G) ∈ D := ⟨z,hz,z,hz,sub_self z⟩
  let H := AddSubgroup.ofSub D ⟨0,h0⟩ (fun a ha b hb => by simpa [sub_eq_add_neg] using hsub a ha b hb)
  refine ⟨H,rfl,hD,H.isOpen_of_mem_nhds (g := 0) ?_⟩
  change K-K ∈ 𝓝 (0:G)
  exact Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top μ K hmea hm hfin

end LpGowers
