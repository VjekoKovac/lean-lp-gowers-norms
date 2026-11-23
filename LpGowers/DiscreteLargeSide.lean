module

public import LpGowers.DiscreteGaussianConstant
public import LpGowers.GaussianCutoff
public import LpGowers.DiscreteAdditiveGap
public import LpGowers.DiscreteRiemannSamples

/-! The two logarithmic bounds at a fixed degree and outer exponent in
Theorem 1.5(b). The sampled Gaussian tests and the uniform upper deficit
play distinct roles in this argument. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LpGowers.Discrete

/-- The dimension-one sample convergence inequalities needed by the lower
estimate. All three limits or bounds are over the side length. -/
def LatticeSampleTests : Prop :=
  ∀ d k : ℕ, 2 ≤ d → ∀ f : ℝ → ℝ≥0, Continuous f →
    Function.support f ⊆ Set.Ioo 0 1 → (∀ x, f x ≤ 1) →
    ∃ A B : ℕ → ℝ,
      Tendsto A atTop (𝓝 (((gowers volume d (k+1:ℕ) f)^((2:ℝ)^d*(k+1:ℕ))).toReal)) ∧
      Tendsto B atTop (𝓝 (((lp volume (criticalExponent d (k+1:ℕ)) (liftNN f))^
        (criticalExponent d (k+1:ℕ))).toReal)) ∧
      ∀ᶠ n : ℕ in atTop, (n:ℝ)^(d+(k+1))*A n ≤ ((n:ℝ)*B n)^(criticalT d (k+1) n)

/-- The lower estimate after passing from bounded Gaussian tests to their
limiting ratio and from the additive logarithmic tolerance to little-o. -/
theorem largeSide_of_sampleTests (hs : LatticeSampleTests) : LargeSideClaim := by
  obtain ⟨c,hc,upper⟩ := criticalT_upper_gap
  refine ⟨c,hc,?_⟩
  intro d p hd hp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  let P := k+1
  let D : ℝ := d+P
  let N : ℝ := (2:ℝ)^d*P
  let C := correction d P
  have hp' : 0 < P := Nat.zero_lt_succ k
  have hC : 0 < C := correction_pos hd hp
  have lower (η : ℝ) (hη : 0 < η) :
      ∀ᶠ n : ℕ in atTop, -C-η ≤ (criticalT d P n-D)*logTwo n := by
    obtain ⟨r,hr,hrC,logTest⟩ := gaussian_log_test d P hp' (η := η/2) (by positivity)
    obtain ⟨f,hf,hSupp,hB,hL,hLt,hUt,hRatio⟩ := exists_unit_interval_gaussian_test d
      (p := (P:ℝ)) (by exact_mod_cast hp') hr hrC
    obtain ⟨ha,hb,hlog⟩ := logTest _ _ hL hLt hUt hRatio
    obtain ⟨A,B,hA,hB',hsamp⟩ := hs d k hd f hf hSupp hB
    have he := eventual_lower_of_sample (D := d+P) ha hb hA hB' (criticalT_tendsto_add d k)
      hsamp (η := η/2) (by positivity)
    filter_upwards [he] with n hn
    have haux : -correction d P-η ≤
        (criticalT d P n-((d+P:ℕ):ℝ))*logTwo n := by linarith only [hn,hlog]
    simpa only [D,C,Nat.cast_add] using haux
  obtain ⟨e,he,hlo⟩ := lower_correction_little_o hC (criticalT d P) lower
  refine ⟨e,he,?_⟩
  filter_upwards [hlo,eventually_ge_atTop 2] with n hn hn'
  exact ⟨hn,upper _ _ _ hd hp hn'⟩

/-- Both bounds in Theorem 1.5(b), with one absolute upper-deficit constant. -/
theorem largeSideClaim : LargeSideClaim :=
  largeSide_of_sampleTests (fun d k hd f => exists_lattice_riemann_samples d k hd (f := f))

end LpGowers.Discrete
