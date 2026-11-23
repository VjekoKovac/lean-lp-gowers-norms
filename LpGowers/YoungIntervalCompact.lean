module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Compactness of bounded interval layers in Young stability

In §5 of M. Christ, *Near-extremizers of Young's inequality for ℝᵈ*,
arXiv:1112.4875, the one-dimensional normalized level-set approximants are
mixtures of indicators of intervals in a fixed bounded set. The last
compactness step of Lemma 5.2 follows by passing to the closed convex hull
of the compact set of interval indicators. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology symmDiff
namespace LpGowers

/-- The indicator of an interval as a Lebesgue `Lᵖ` element. -/
def youngInterval (p : ℝ≥0∞) (a b : ℝ) : Lp ℝ p (volume : Measure ℝ) :=
  indicatorConstLp (s := Ioc a b) p measurableSet_Ioc (by rw [Real.volume_Ioc]; finiteness) (1:ℝ)

private theorem interval_symmetricDifference (a b c d : ℝ) :
    volume (Ioc a b ∆ Ioc c d) ≤ ENNReal.ofReal |c-a| + ENNReal.ofReal |d-b| := by
  have sub : Ioc a b ∆ Ioc c d ⊆ uIoc a c ∪ uIoc b d := by
    intro x hx
    simp only [mem_symmDiff,mem_Ioc,mem_union,uIoc] at hx ⊢
    rcases le_total a c with h | h <;> rcases le_total b d with j | j <;>
      simp only [min_eq_left h,min_eq_right h,max_eq_left h,max_eq_right h,
        min_eq_left j,min_eq_right j,max_eq_left j,max_eq_right j] <;> grind
  exact ((measure_mono sub).trans (measure_union_le _ _)).trans_eq (by rw [Real.volume_uIoc,Real.volume_uIoc])

/-- The entire two-parameter family is continuous, including reversed or
degenerate intervals, which represent the zero element. -/
theorem continuous_youngInterval (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) :
    Continuous (fun z : ℝ×ℝ => youngInterval p z.1 z.2) := by
  unfold youngInterval
  apply continuous_indicatorConstLp_set hp
  intro z
  have H : Continuous (fun w : ℝ×ℝ => ENNReal.ofReal |z.1-w.1|+ENNReal.ofReal |z.2-w.2|) :=
    (ENNReal.continuous_ofReal.comp ((continuous_const.sub continuous_fst).abs)).add
      (ENNReal.continuous_ofReal.comp ((continuous_const.sub continuous_snd).abs))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun _ => (0:ℝ≥0∞)) (h:=fun w : ℝ×ℝ =>
      ENNReal.ofReal |z.1-w.1|+ENNReal.ofReal |z.2-w.2|) tendsto_const_nhds
  · simpa only [sub_self,abs_zero,ENNReal.ofReal_zero,add_zero] using (H.tendsto z)
  · exact fun _ => zero_le
  · exact fun w => interval_symmetricDifference w.1 w.2 z.1 z.2

/-- One compact set of `Lᵖ` contains all probability averages of indicators
of intervals with endpoints in `[a,b]`. The probability space and its
distribution of endpoints can vary arbitrarily. -/
theorem compact_interval_mixtures (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (a b : ℝ) :
    ∃ K : Set (Lp ℝ p (volume : Measure ℝ)), IsCompact K ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (u : Ω → ℝ×ℝ), AEStronglyMeasurable u ν →
        (∀ᵐ t ∂ν,u t ∈ Icc a b ×ˢ Icc a b) →
        (∫ t, youngInterval p (u t).1 (u t).2 ∂ν) ∈ K := by
  let I := Icc a b ×ˢ Icc a b
  let Y := fun z : ℝ×ℝ => youngInterval p z.1 z.2
  let S := Y '' I
  have hc : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (continuous_youngInterval p hp)
  let K := closure (convexHull ℝ S)
  have hK : IsCompact K := isCompact_iff_totallyBounded_isComplete.mpr
    ⟨hc.totallyBounded.convexHull.closure,isClosed_closure.isComplete⟩
  refine ⟨K,hK,?_⟩
  intro Ω _ ν _ u hu hi
  have ha : ∀ᵐ t ∂ν,Y (u t) ∈ S := hi.mono fun _ ht => mem_image_of_mem Y ht
  have hconv : Convex ℝ K := (convex_convexHull ℝ S).closure
  obtain ⟨C,hC⟩ := hc.isBounded.exists_norm_le
  have hInt : Integrable (fun t => Y (u t)) ν := Integrable.of_bound
    ((continuous_youngInterval p hp).comp_aestronglyMeasurable hu) C (ha.mono fun _ ht => hC _ ht)
  exact hconv.integral_mem isClosed_closure (ha.mono fun _ ht => subset_closure (subset_convexHull ℝ S ht)) hInt

/-- Replacing almost every superlevel set by a nearby interval costs at most
the common symmetric-difference error to the power `1/p`, measured in strong
`Lᵖ` after integration over the levels. -/
theorem interval_layer_error (p : ℝ≥0∞) [hp₁ : Fact (1≤p)] (hp : p≠⊤)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : Ω → Set ℝ) (hA : ∀ t, MeasurableSet (A t)) (hfin : ∀ t, volume (A t)≠⊤)
    (u : Ω → ℝ×ℝ) (δ : ℝ≥0)
    (hδ : ∀ᵐ t ∂ν, volume (A t ∆ Ioc (u t).1 (u t).2) ≤ δ)
    (ha : Integrable (fun t => indicatorConstLp p (hA t) (hfin t) (1:ℝ)) ν)
    (hu : Integrable (fun t => youngInterval p (u t).1 (u t).2) ν) :
    dist (∫ t, indicatorConstLp p (hA t) (hfin t) (1:ℝ) ∂ν)
      (∫ t, youngInterval p (u t).1 (u t).2 ∂ν) ≤ (δ:ℝ)^(1/p.toReal) := by
  let F := fun t => indicatorConstLp p (hA t) (hfin t) (1:ℝ)
  let G := fun t => youngInterval p (u t).1 (u t).2
  have hbound : ∀ᵐ t ∂ν, ‖F t-G t‖ ≤ (δ:ℝ)^(1/p.toReal) := by
    filter_upwards [hδ] with t ht
    rw [← dist_eq_norm]
    unfold F G youngInterval
    rw [dist_indicatorConstLp_eq_norm,norm_indicatorConstLp (zero_lt_one.trans_le hp₁.out).ne' hp,
      norm_one,one_mul]
    apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (by positivity)
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top ht).trans_eq (by simp)
  rw [dist_eq_norm, ← integral_sub ha hu]
  apply (norm_integral_le_integral_norm (fun t => F t-G t)).trans
  simpa using integral_mono_ae (ha.sub hu).norm (integrable_const ((δ:ℝ)^(1/p.toReal))) hbound

/-- Strong precompactness of profiles approximable by uniformly bounded interval
layers at every tolerance. The bounds on the endpoints and total layer height
can depend on the required approximation. -/
theorem subsequence_of_interval_approximation (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (F : ℕ → Lp ℝ p (volume : Measure ℝ))
    (h : ∀ ε : ℝ, 0<ε → ∃ a b c : ℝ, ∀ᶠ k : ℕ in atTop,
      ∃ u : Ω → ℝ×ℝ, AEStronglyMeasurable u ν ∧ (∀ᵐ t ∂ν, u t ∈ Icc a b ×ˢ Icc a b) ∧
        dist (F k) (c • ∫ t, youngInterval p (u t).1 (u t).2 ∂ν) ≤ ε) :
    ∃ v : Lp ℝ p (volume : Measure ℝ), ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (F ∘ σ) atTop (𝓝 v) := by
  classical
  have hTot : TotallyBounded (range F) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨a,b,c,h⟩ := h (ε/2) (half_pos hε)
    obtain ⟨m,hm⟩ := eventually_atTop.mp h
    obtain ⟨K,hK,hmixture⟩ := compact_interval_mixtures p hp a b
    let T := (fun v : Lp ℝ p (volume : Measure ℝ) => c • v) '' K
    have hT : IsCompact T := hK.image (continuous_const_smul c)
    obtain ⟨U,hU,hcover⟩ := Metric.totallyBounded_iff.mp hT.totallyBounded (ε/2) (half_pos hε)
    let P := F '' Set.Iio m
    refine ⟨P ∪ U, ((Set.finite_Iio m).image F).union hU,?_⟩
    rintro _ ⟨k,rfl⟩
    simp only [mem_iUnion]
    by_cases hk : k<m
    · exact ⟨F k,Or.inl ⟨k,hk,rfl⟩,Metric.mem_ball_self hε⟩
    · obtain ⟨u,hu,hi,hclose⟩ := hm k (Nat.le_of_not_gt hk)
      let v := ∫ t, youngInterval p (u t).1 (u t).2 ∂ν
      have hv : c • v ∈ T := ⟨v,hmixture ν u hu hi,rfl⟩
      have hnear := hcover hv
      simp only [mem_iUnion,Metric.mem_ball] at hnear
      obtain ⟨w,hw,hvw⟩ := hnear
      exact ⟨w,Or.inr hw,(dist_triangle (F k) (c • v) w).trans_lt (by linarith only [hclose,hvw])⟩
  have hK : IsCompact (closure (range F)) := isCompact_iff_totallyBounded_isComplete.mpr
    ⟨hTot.closure,isClosed_closure.isComplete⟩
  obtain ⟨v,_,σ,hσ,H⟩ := hK.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  exact ⟨v,σ,hσ,H⟩

end LpGowers
