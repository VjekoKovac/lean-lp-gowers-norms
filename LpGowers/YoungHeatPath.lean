module

public import LpGowers.HeatApproximation
import Mathlib.Tactic

/-! # The heat path from a probability density to the Gaussian family

The conserved mass turns pointwise convergence into strong convergence, both
locally in positive heat time and in the dilated coordinates at large time. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter GeometricBrascampLieb
open scoped Topology

namespace LpGowers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Extend the forward heat flow at its initial time by its initial datum. -/
def heatPath (f : E → ℝ) (t : ℝ) : E → ℝ :=
  if t ≤ 0 then f else heatConvolution f t

/-- Unit-mass heat kernel on the underlying real Hilbert space. -/
def heatGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (t : ℝ) (x : E) : ℝ :=
  heatNormalization (E := E) t * Real.exp (-(4*t)⁻¹ * ‖x‖^2)

private lemma common_mass_L1_limit {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter ι} [l.IsCountablyGenerated] {u : ι → X → ℝ} {g : X → ℝ}
    (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x)
    (hu : ∀ᶠ i in l, Integrable (u i) μ ∧ (∀ x, 0 ≤ u i x) ∧
      ∫ x, u i x ∂μ = ∫ x, g x ∂μ)
    (hpt : ∀ x, Tendsto (fun i => u i x) l (𝓝 (g x))) :
    Tendsto (fun i => ∫ x, ‖u i x-g x‖ ∂μ) l (𝓝 0) := by
  let m i x := min (u i x) (g x)
  have hmin : Tendsto (fun i => ∫ x, m i x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · filter_upwards [hu] with i hi
      exact (hi.1.inf hg).aestronglyMeasurable
    · filter_upwards [hu] with i hi
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hi.2.1 x) (hg0 x))]
        exact min_le_right _ _
    · exact hg
    · exact Eventually.of_forall fun x => by
        simpa only [min_self] using (hpt x).min (tendsto_const_nhds (x := g x))
  have hL := (tendsto_const_nhds (x := (∫ x, g x ∂μ) + (∫ x, g x ∂μ))).sub (hmin.const_mul 2)
  have hzero : (∫ x,g x ∂μ) + (∫ x,g x ∂μ) - 2*(∫ x,g x ∂μ) = 0 := by ring
  rw [hzero] at hL
  apply hL.congr'
  filter_upwards [hu] with i ⟨hui,_,hmass⟩
  have hab (a b : ℝ) : ‖a-b‖ = a+b-2*min a b := by
    rw [Real.norm_eq_abs]
    rcases le_total a b with h|h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [hab]
  have h1 : Integrable (fun x => u i x + g x) μ := hui.add hg
  have h2 : Integrable (fun x => 2 * min (u i x) (g x)) μ := (hui.inf hg).const_mul 2
  rw [integral_sub h1 h2, integral_add hui hg, hmass, integral_const_mul]

/-- Strong continuity of the heat path, including its original datum at time zero. -/
theorem heatPath_L1_continuous {f : E → ℝ} (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun s => ∫ x, ‖heatPath f s x - heatPath f t x‖) (𝓝[Ici 0] t) (𝓝 0) := by
  rcases ht.eq_or_lt with rfl|ht
  · rw [← insert_Ioi, nhdsWithin_insert, tendsto_sup]
    constructor
    · simpa using (tendsto_pure_nhds (fun s => ∫ x, ‖heatPath f s x - heatPath f 0 x‖) (0:ℝ))
    apply tendsto_iff_seq_tendsto.mpr
    intro τ hτ
    have hpos : ∀ᶠ i in atTop, 0 < τ i := hτ eventually_mem_nhdsWithin
    let σ i := if 0 < τ i then τ i else 1
    have he : σ =ᶠ[atTop] τ := hpos.mono fun i hi => ite_eq_left hi
    have hl := heatConvolution_tendsto_L1 hf hn σ (hτ.congr' he.symm)
      (fun i => by dsimp [σ]; split_ifs <;> positivity)
    apply hl.congr'
    filter_upwards [he,hpos] with i he' hi
    simp [Function.comp_apply,heatPath,not_le.mpr hi,he']
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hu : ∀ᶠ s in 𝓝 t, 0 < s := eventually_gt_nhds ht
    rw [show heatPath f t = heatConvolution f t by simp [heatPath,not_le.mpr ht]]
    apply common_mass_L1_limit (heatConvolution_integrable hf ht)
      (fun x => mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg hn _ _))
    · filter_upwards [hu] with s hs
      rw [show heatPath f s = heatConvolution f s by simp [heatPath,not_le.mpr hs]]
      exact ⟨heatConvolution_integrable hf hs,
        fun x => mul_nonneg (Real.exp_pos _).le (gaussianConvolution_nonneg hn _ _),
        (integral_heatConvolution hf hs).trans (integral_heatConvolution hf ht).symm⟩
    · intro x
      exact (heatConvolution_hasDerivAt hf ht x).continuousAt.tendsto.congr'
        (hu.mono fun s hs => by simp [heatPath,not_le.mpr hs])

omit [MeasurableSpace E] [BorelSpace E] in
private lemma heatGaussian_scale {a : ℝ} (ha : 0 < a) (x : E) :
    heatGaussian E (a^2) (a • x) = (a^Module.finrank ℝ E)⁻¹ * heatGaussian E 1 x := by
  have h := gaussian_exponent_scale ha x (0:E)
  simp only [smul_zero,sub_zero] at h
  simp only [heatGaussian,heatNormalization_scale ha,exp_neg_nat_mul_log ha, h, mul_one]
  ring_nf

private lemma rescaled_mass {f : E → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) :
    Integrable (rescaledHeat f a⁻¹) ∧ (∫ x, rescaledHeat f a⁻¹ x) = ∫ x, f x := by
  let D := Module.finrank ℝ E
  have haD : (a^D) ≠ 0 := pow_ne_zero _ ha.ne'
  have he (x : E) : rescaledHeat f a⁻¹ x = a^D * heatConvolution f (a^2) (a • x) := by
    rw [heatConvolution_scale f ha, exp_neg_nat_mul_log ha]
    simp [D,ha.ne']
  rw [show rescaledHeat f a⁻¹ = _ from funext he]
  have hi := heatConvolution_integrable hf (sq_pos_of_pos ha)
  refine ⟨((integrable_comp_smul_iff volume _ ha.ne').2 hi).const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume _ a (hR := ha.le), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ haD, one_mul, integral_heatConvolution hf (sq_pos_of_pos ha)]

/-- A unit-mass heat convolution approaches the Gaussian at its *current*
time in absolute L¹ distance, with arbitrary integrable nonnegative initial data. -/
theorem heatConvolution_large_time_L1 {f : E → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (hm : (∫ x, f x) = 1) :
    Tendsto (fun t => ∫ x, ‖heatConvolution f t x - heatGaussian E t x‖) atTop (𝓝 0) := by
  let K (x : E) := heatGaussian E 1 x
  have hK : Integrable K := by
    dsimp [K,heatGaussian]
    apply Integrable.const_mul
    simpa using integrable_gaussian_shift (0:E) (by norm_num : 0 < (4*(1:ℝ))⁻¹)
  have hKi : (∫ x, K x) = 1 := by
    simpa only [K,heatGaussian,mul_one,one_div] using integral_normalized_gaussian (E := E)
  have hK0 x : 0 ≤ K x := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hl : Tendsto (fun a : ℝ => ∫ x, ‖rescaledHeat f a⁻¹ x-K x‖) atTop (𝓝 0) := by
    apply common_mass_L1_limit hK hK0
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      obtain ⟨hi,hh⟩ := rescaled_mass hf ha
      exact ⟨hi, fun x => (rescaledHeat_pos hf hf0 (hm ▸ zero_lt_one) _ _).le, hh.trans (hm.trans hKi.symm)⟩
    · intro x
      have hc := ((rescaledHeat_continuous hf).comp (continuous_id.prodMk (continuous_const (y := x)))).tendsto (0:ℝ)
      have h := hc.comp (tendsto_inv_atTop_zero : Tendsto (fun a:ℝ => a⁻¹) atTop (𝓝 0))
      change Tendsto (fun a:ℝ => rescaledHeat f a⁻¹ x) atTop (𝓝 (rescaledHeat f 0 x)) at h
      simpa [K,heatGaussian,rescaledHeat_zero,hm] using h
  have he : Tendsto (fun a : ℝ => ∫ x, ‖heatConvolution f (a^2) x - heatGaussian E (a^2) x‖) atTop (𝓝 0) := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
    let Q x := ‖heatConvolution f (a^2) x - heatGaussian E (a^2) x‖
    have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E) Q a (hR := ha.le)
    have hs : ∀ x, Q (a • x) = (a^Module.finrank ℝ E)⁻¹ * ‖rescaledHeat f a⁻¹ x - K x‖ := by
      intro x
      dsimp only [Q,K]
      rw [heatConvolution_scale f ha,exp_neg_nat_mul_log ha,heatGaussian_scale ha,← mul_sub,norm_mul,
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (a^Module.finrank ℝ E)⁻¹)]
    simp_rw [hs] at h
    rw [integral_const_mul,smul_eq_mul] at h
    exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ ha.ne')) h
  apply (he.comp Real.tendsto_sqrt_atTop).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  simp [Function.comp_apply,Real.sq_sqrt ht]

end LpGowers
