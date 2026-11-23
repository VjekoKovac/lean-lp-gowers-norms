module

public import GeometricBrascampLieb.L1Approximation
public import GeometricBrascampLieb.SmallTimeEndpoint
import Mathlib.Tactic

/-! # Approximation by normalized Euclidean heat convolution in L¹

A compact continuous approximation controls general integrable inputs by
the L¹ contraction. For compact continuous nonnegative inputs the pointwise
small-time limit and conservation of mass imply convergence in L¹.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter GeometricBrascampLieb
open scoped Topology ENNReal
namespace LpGowers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem heatConvolution_L1_contraction {f g : E → ℝ} (hf : Integrable f) (hg : Integrable g)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖heatConvolution f t x - heatConvolution g t x‖) ≤ ∫ x, ‖f x-g x‖ := by
  let b := (4*t)⁻¹
  let k (x y : E) := Real.exp (-b * ‖x-y‖^2)
  let h := fun x => ‖f x - g x‖
  have hi : Integrable h := (hf.sub hg).norm
  rw [← integral_heatConvolution hi ht]
  apply integral_mono ((heatConvolution_integrable hf ht).sub (heatConvolution_integrable hg ht)).norm
    (heatConvolution_integrable hi ht)
  intro x
  change ‖heatNormalization (E := E) t * (∫ y, f y * k x y) -
    heatNormalization (E := E) t * (∫ y, g y * k x y)‖ ≤
    heatNormalization (E := E) t * ∫ y, ‖f y - g y‖ * k x y
  have hfk : Integrable (fun y => f y * k x y) := gaussianConvolution_integrand_integrable hf (by dsimp [b]; positivity) x
  have hgk : Integrable (fun y => g y * k x y) := gaussianConvolution_integrand_integrable hg (by dsimp [b]; positivity) x
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos (show 0 < heatNormalization (E := E) t from Real.exp_pos _),
    ← integral_sub hfk hgk]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  convert norm_integral_le_integral_norm (fun y => f y*k x y-g y*k x y) using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (k x y), abs_of_pos (show 0 < k x y from Real.exp_pos _)]

private theorem heatConvolution_L1_compact {g : E → ℝ} (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) (hc : Continuous g) (hs : HasCompactSupport g)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝[>] 0)) (hτ0 : ∀ n, 0 < τ n) :
    Tendsto (fun n => ∫ x, ‖heatConvolution g (τ n) x - g x‖) atTop (𝓝 0) := by
  let u n := heatConvolution g (τ n)
  have hui n : Integrable (u n) := heatConvolution_integrable hg (hτ0 n)
  have hnn n x : 0 ≤ u n x := mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg hg0 _ _)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hc
  let m n := fun x => min (u n x) (g x)
  have hmi n : Integrable (m n) := (hui n).inf hg
  have hlim : Tendsto (fun n => ∫ x, m n x) atTop (𝓝 (∫ x, g x)) := by
    apply tendsto_integral_of_dominated_convergence g (fun n => (hmi n).aestronglyMeasurable) hg
    · intro n
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn n x) (hg0 x))]
        exact min_le_right _ _
    · exact Eventually.of_forall fun x => by
        simpa only [m,u,Function.comp_apply,min_self] using
          (((heatConvolution_tendsto_zero hc hC x).comp hτ).min (tendsto_const_nhds (x := g x)))
  have hrep n : (∫ x, ‖u n x-g x‖) = (∫ x, g x)+(∫ x, g x)-2*(∫ x, m n x) := by
    have he (x) : ‖u n x-g x‖ = u n x + g x - 2*m n x := by
      dsimp only [m]; rw [Real.norm_eq_abs]
      cases le_total (u n x) (g x) with
      | inl h => rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      | inr h => rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp_rw [he]
    have ha : Integrable (fun x => u n x + g x) := (hui n).add hg
    rw [integral_sub ha ((hmi n).const_mul 2),integral_add (hui n) hg,
      integral_const_mul,show (∫ x, u n x) = ∫ x, g x from integral_heatConvolution hg (hτ0 n)]
  simp_rw [show ∀ n, (∫ x, ‖heatConvolution g (τ n) x-g x‖) =
    (∫ x, g x)+(∫ x, g x)-2*(∫ x, m n x) from hrep]
  convert (tendsto_const_nhds (x := (∫ x, g x)+(∫ x, g x))).sub (hlim.const_mul 2) using 1
  ring_nf

/-- Finite-mass nonnegative functions are approximated in L¹ by their heat regularizations
along any positive sequence of times tending to zero. -/
theorem heatConvolution_tendsto_L1 {f : E → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝[>] 0)) (hτ0 : ∀ n, 0 < τ n) :
    Tendsto (fun n => ∫ x, ‖heatConvolution f (τ n) x - f x‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g,hgc,hgs,hg0,hgi,herr⟩ := exists_nonneg_compact_approx hf hf0
    (show 0 < ε/4 by positivity)
  have hg := heatConvolution_L1_compact hgi hg0 hgc hgs τ hτ hτ0
  filter_upwards [hg.eventually_lt_const (show 0 < ε/4 by positivity)] with n hn
  have hfi := heatConvolution_integrable hf (hτ0 n)
  have hhi := heatConvolution_integrable hgi (hτ0 n)
  have heq : (∫ x, ‖g x-f x‖) = ∫ x, ‖f x-g x‖ := by simp_rw [norm_sub_rev (g _) (f _)]
  have htri (a b c : ℝ) : ‖a-c‖ ≤ ‖a-b‖ + ‖b-c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  have hfirst : Integrable (fun x => ‖heatConvolution f (τ n) x - heatConvolution g (τ n) x‖ +
      ‖heatConvolution g (τ n) x-g x‖) := (hfi.sub hhi).norm.add (hhi.sub hgi).norm
  have h := integral_mono (hfi.sub hf).norm (hfirst.add (hgi.sub hf).norm)
    (fun x => (htri _ (g x) _).trans (add_le_add_left
      (htri (heatConvolution f (τ n) x) (heatConvolution g (τ n) x) (g x)) _))
  change (∫ x, ‖heatConvolution f (τ n) x - f x‖) ≤
    (∫ x, ((‖heatConvolution f (τ n) x - heatConvolution g (τ n) x‖ +
      ‖heatConvolution g (τ n) x-g x‖) + ‖g x-f x‖)) at h
  have ha : (∫ x, ‖heatConvolution f (τ n) x-heatConvolution g (τ n) x‖ +
      ‖heatConvolution g (τ n) x-g x‖) =
      (∫ x, ‖heatConvolution f (τ n) x-heatConvolution g (τ n) x‖)+
      (∫ x, ‖heatConvolution g (τ n) x-g x‖) :=
    integral_add (f := fun x => ‖heatConvolution f (τ n) x-heatConvolution g (τ n) x‖)
      (g := fun x => ‖heatConvolution g (τ n) x-g x‖) (hfi.sub hhi).norm (hhi.sub hgi).norm
  rw [integral_add hfirst (show Integrable (fun x => ‖g x - f x‖) from (hgi.sub hf).norm),ha,heq] at h
  have hcon := heatConvolution_L1_contraction hf hgi (hτ0 n)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  linarith

/-- A sequence of strictly positive heat times tends to zero and its regularizations
converge to the given integrable function almost everywhere. -/
theorem exists_heatConvolution_subsequence_ae {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝[>] 0) ∧
      ∀ᵐ x, Tendsto (fun n => heatConvolution f (t n) x) atTop (𝓝 (f x)) := by
  let τ := fun n : ℕ => 1/((n:ℝ)+1)
  have hτ0 n : 0 < τ n := by dsimp [τ]; positivity
  have hτ : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hτ0⟩
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp (heatConvolution_tendsto_L1 hf hf0 τ hτ hτ0)
  have hLp : Tendsto (fun n => eLpNorm (heatConvolution f (τ n)-f) 1) atTop (𝓝 0) := by
    convert h using 1
    · ext n
      have hi := (heatConvolution_integrable hf (hτ0 n)).sub hf
      rw [eLpNorm_one_eq_lintegral_eNorm hi.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_eNorm hi]
      rfl
    · simp
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hLp).exists_seq_tendsto_ae
  exact ⟨τ ∘ s, fun n => hτ0 _, hτ.comp hs.tendsto_atTop, hae⟩

end LpGowers
