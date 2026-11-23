module

public import LpGowers.LatticeRiemann
public import LpGowers.DiscreteTensorization
public import LpGowers.LogMoments

/-! # Sampling a continuous test in the discrete Gowers energy

The sample lives on a one-dimensional integer lattice. Its complete raw
moment has one integer coordinate for each common shift and each base point.
The corresponding integrand is continuous, and it vanishes outside a fixed
compact box if the original test is supported in the open unit interval. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set Bornology
open scoped BigOperators ENNReal NNReal Topology
namespace LpGowers.Discrete

/-- One cube vertex, with all shifts and base points indexed by one sum type. -/
def packedVertex {G : Type*} [AddCommMonoid G] {d p : ℕ} (z : Fin d ⊕ Fin p → G)
    (j : Fin p) (s : Finset (Fin d)) :=
  z (.inr j)+∑ i ∈ s,z (.inl i)

/-- Real-valued configuration density of a nonnegative function on the line. -/
def realCubeDensity (d p : ℕ) (f : ℝ → ℝ≥0) (z : Fin d ⊕ Fin p → ℝ) : ℝ :=
  ∏ j, ∏ s, (f (packedVertex z j s) : ℝ)

theorem continuous_realCubeDensity (d p : ℕ) {f : ℝ → ℝ≥0} (hf : Continuous f) :
    Continuous (realCubeDensity d p f) := by
  unfold realCubeDensity packedVertex
  fun_prop

private theorem realCubeDensity_outside (d k : ℕ) {f : ℝ → ℝ≥0}
    (hs : Function.support f ⊆ Set.Ioo 0 1) (z : Fin d ⊕ Fin (k+1) → ℝ) :
    z ∉ Set.Icc (fun _ => -1) (fun _ => 1) → realCubeDensity d (k+1) f z=0 := by
  intro hz
  contrapose! hz
  have hn j s : f (packedVertex z j s) ≠ 0 := by
    intro h
    apply hz
    unfold realCubeDensity
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [h]
  have hb (j : Fin (k+1)) : 0 < z (.inr j) ∧ z (.inr j) < 1 := by
    simpa [packedVertex] using hs (hn j ∅)
  have hstep (i : Fin d) : -1 ≤ z (.inl i) ∧ z (.inl i) ≤ 1 := by
    have H := hs (hn 0 {i})
    change 0<packedVertex z 0 {i} ∧ packedVertex z 0 {i}<1 at H
    simp only [packedVertex,Finset.sum_singleton] at H
    constructor <;> linarith [hb 0]
  constructor
  · rintro (i|j)
    · exact (hstep i).1
    · change -1≤z (.inr j); linarith [hb j]
  · rintro (i|j)
    · exact (hstep i).2
    · exact (hb j).2.le

/-- Riemann convergence for the actual configuration integrand, including
all repeated base points and all zero increments. -/
theorem tendsto_sampled_configuration (d k : ℕ) {f : ℝ → ℝ≥0} (hf : Continuous f)
    (hs : Function.support f ⊆ Set.Ioo 0 1) :
    Tendsto (fun n : ℕ => (∑' z : Fin d ⊕ Fin (k+1) → ℤ, realCubeDensity d (k+1) f (gridPoint n z)) /
      (n:ℝ)^(d+(k+1))) atTop (𝓝 (∫ z, realCubeDensity d (k+1) f z)) := by
  let S : Set (Fin d ⊕ Fin (k+1) → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have h := tendsto_lattice_sum S _ (continuous_realCubeDensity d (k+1) hf) isCompact_Icc.isBounded
    measurableSet_Icc ((convex_Icc ..).addHaar_frontier volume) (realCubeDensity_outside d k hs)
  simpa only [Fintype.card_sum,Fintype.card_fin] using h

/-- Identification of the limiting raw configuration integral with the exact
`2^d p`-power of the continuous Gowers functional. -/
theorem continuous_configuration_moment (d k : ℕ) {f : ℝ → ℝ≥0} (hf : Continuous f) :
    (∫⁻ z, ENNReal.ofReal (realCubeDensity d (k+1) f z)) =
      (gowers volume d (k+1:ℕ) f) ^ ((2:ℝ)^d*(k+1:ℕ)) := by
  let μ := (volume : Measure ℝ)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin (k+1) => ℝ)
  have he := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin (k+1) => ℝ)
  let P := fun z => ENNReal.ofReal (realCubeDensity d (k+1) f z)
  have hP : Measurable P := ENNReal.measurable_ofReal.comp (continuous_realCubeDensity d (k+1) hf).measurable
  let Y := fun (h : Fin d → ℝ) (x : ℝ) => cubeProduct d f h x
  have hY (h : Fin d → ℝ) : Measurable (Y h) :=
    measurable_cubeProduct_comp hf.measurable d (fun i _ => h i) (fun _ => measurable_const) id measurable_id
  have hpoint (h : Fin d → ℝ) (x : Fin (k+1) → ℝ) :
      P (e.symm (h,x)) = ∏ j, Y h (x j) := by
    unfold P realCubeDensity
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg (fun s _ => (f _).coe_nonneg))]
    apply Finset.prod_congr rfl
    intro j _
    rw [ENNReal.ofReal_prod_of_nonneg (fun s _ => (f _).coe_nonneg)]
    simp only [Y,cubeProduct_vertices,ENNReal.ofReal_coe_nnreal]
    rfl
  rw [← (he.symm e).lintegral_comp hP]
  change (∫⁻ z, P (e.symm z) ∂(volume.prod volume)) = _
  rw [lintegral_prod (fun z => P (e.symm z)) (hP.comp e.symm.measurable).aemeasurable,
    gowers_moment_power (p:=(k+1:ℕ)) μ d (by positivity) f]
  apply lintegral_congr
  intro h
  simp_rw [hpoint]
  rw [show (∫⁻ x : Fin (k+1) → ℝ, ∏ j, Y h (x j)) = ∏ _ : Fin (k+1), ∫⁻ y, Y h y ∂μ
    from lintegral_pi_separated μ (k+1) _ (fun _ => hY h)]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.rpow_natCast]
  rfl

end LpGowers.Discrete
