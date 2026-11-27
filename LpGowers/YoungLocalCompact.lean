module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-! Local sequential compactness of approximate fixed points, used at a
Gaussian for the nonlinear Euler equation of the sharp Young inequality. -/
@[expose] public section
open Set Filter
open scoped Topology
namespace LpGowers

/-- If a self-map on a Banach space has compact strict derivative at a point,
all approximate fixed-point sequences in some fixed neighborhood of that
point have convergent subsequences. -/
theorem exists_local_approx_fixed_precompact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : E → E} {G : E} {L : E →L[ℝ] E}
    (hd : HasStrictFDerivAt T L G) (hc : IsCompactOperator L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℕ → E, (∀ k, dist (u k) G < ε) →
      Tendsto (fun k => u k - T (u k)) atTop (𝓝 0) →
      ∃ g : E, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (u ∘ σ) atTop (𝓝 g) := by
  let R := fun x => T x - L x
  have hR : HasStrictFDerivAt R (0 : E →L[ℝ] E) G := by simpa [R,Pi.sub_def] using hd.sub L.hasStrictFDerivAt
  obtain ⟨S,hS,hLip⟩ := hR.exists_lipschitzOnWith_of_nnNorm_lt (1/2) (by norm_num)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨ε,hε,?_⟩
  intro u hu hres
  obtain ⟨K,hK,himage⟩ := hc.image_subset_compact_of_bounded (f := L.toLinearMap)
    (Metric.isBounded_ball (x := G) (r := ε))
  obtain ⟨g,_,σ,hσ,hL⟩ := hK.tendsto_subseq (fun k => himage ⟨u k,hu k,rfl⟩)
  let v := u ∘ σ
  let y := fun k => (v k - T (v k)) + L (v k)
  have hy : Tendsto y atTop (𝓝 g) := by
    simpa only [zero_add,y,v,Function.comp_apply,ContinuousLinearMap.coe_coe] using (hres.comp hσ.tendsto_atTop).add hL
  have hpair (j k : ℕ) : dist (v j) (v k) ≤ 2 * dist (y j) (y k) := by
    have h1 := hLip.dist_le_mul (v j) (hball (hu (σ j))) (v k) (hball (hu (σ k)))
    change dist (R (v j)) (R (v k)) ≤ _ at h1
    have hre (i : ℕ) : v i = y i + R (v i) := by dsimp [y,R]; abel
    have h2 : dist (v j) (v k) ≤ dist (y j) (y k) + dist (R (v j)) (R (v k)) := by
      conv_lhs => rw [hre j, hre k]
      exact dist_add_add_le _ _ _ _
    norm_num at h1
    linarith
  have hv : CauchySeq v := by
    refine Metric.cauchySeq_iff.mpr fun δ hδ => ?_
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hy.cauchySeq (δ/2) (by positivity)
    exact ⟨N,fun j hj k hk => by linarith only [hN j hj k hk,hpair j k]⟩
  obtain ⟨g',hg'⟩ := cauchySeq_tendsto_of_complete hv
  exact ⟨g',σ,hσ,hg'⟩

end LpGowers
