module

public import LpGowers.HolderStability
public import LpGowers.Degree
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-! Passing quantitative Hölder stability from real integrable densities to
the extended nonnegative integrals used for the autocorrelations. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
namespace LpGowers

/-- For finite masses the lower integral of the absolute density difference
equals the ordinary integral on the almost-everywhere finite representatives. -/
theorem l1DensityError_eq_ofReal_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : X → ℝ≥0∞} (ha : AEMeasurable A μ) (hb : AEMeasurable B μ)
    (hA : (∫⁻ x, A x ∂μ) ≠ ⊤) (hB : (∫⁻ x, B x ∂μ) ≠ ⊤) :
    l1DensityError μ A B = ENNReal.ofReal (∫ x, |(A x).toReal - (B x).toReal| ∂μ) := by
  have hi : Integrable (fun x => |(A x).toReal - (B x).toReal|) μ := ((integrable_toReal_of_lintegral_ne_top ha hA).sub (integrable_toReal_of_lintegral_ne_top hb hB)).abs
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => abs_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top' ha hA, ae_lt_top' hb hB] with x hx hy
  rcases le_total (B x) (A x) with h | h
  · rw [tsub_eq_zero_of_le h, add_zero,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hx.ne h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne,
      ENNReal.ofReal_toReal hy.ne]
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hy.ne h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne,
      ENNReal.ofReal_toReal hx.ne]

/-- Uniform stability for near saturation of weighted Hölder with density
masses at most one. This includes the probability densities from §5 and
the contracted, subnormalized products in the Loomis–Whitney argument. -/
theorem holder_stability_ennreal {ι : Type*} [Fintype ι] [Nonempty ι] (γ : ι → ℝ)
    (hγ : ∀ i, 0 < γ i) (hs : ∑ i, γ i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : ι → X → ℝ≥0∞),
    (∀ i, AEMeasurable (u i) μ) → (∀ i, (∫⁻ x, u i x ∂μ) ≤ 1) →
    ENNReal.ofReal (1-ε) ≤ ∫⁻ x, ∏ j, (u j x)^γ j ∂μ → ∀ i,
    l1DensityError μ (u i) (fun x => ∏ j, (u j x)^γ j) ≤ ENNReal.ofReal η ∧
      ∀ j, l1DensityError μ (u i) (u j) ≤ ENNReal.ofReal η := by
  obtain ⟨δ,hd,H⟩ := holder_stability γ hγ hs hη
  refine ⟨δ, hd, ?_⟩
  intro ε he hε X _ μ u hu hn hnear
  let v := fun i x => (u i x).toReal
  let P := fun x => ∏ j, (u j x)^γ j
  have hv i : (∫⁻ x, u i x ∂μ) ≠ ⊤ := ((hn i).trans_lt ENNReal.one_lt_top).ne
  have hP : AEMeasurable P μ := Finset.aemeasurable_fun_prod _ fun i _ => (hu i).pow_const _
  have hbound : (∫⁻ x, P x ∂μ) ≤ 1 := by
    apply (ENNReal.lintegral_prod_norm_pow_le Finset.univ (fun i _ => hu i) hs (fun i _ => (hγ i).le)).trans
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod
      (fun i (_ : i ∈ Finset.univ) => ENNReal.rpow_le_one (hn i) (hγ i).le)
  have hPfin := (hbound.trans_lt ENNReal.one_lt_top).ne
  have heq (x) : (P x).toReal = ∏ j, (v j x)^γ j := by
    simp only [P, ENNReal.toReal_prod, ← ENNReal.toReal_rpow, v]
  have hi (i) : Integrable (v i) μ := integrable_toReal_of_lintegral_ne_top (hu i) (hv i)
  have hn' i : ∫ x, v i x ∂μ ≤ 1 := by
    rw [show (∫ x, v i x ∂μ) = (∫⁻ x, u i x ∂μ).toReal from integral_toReal (hu i) (ae_lt_top' (hu i) (hv i))]
    simpa using ENNReal.toReal_mono (by simp) (hn i)
  have hlower : 1 - ε ≤ ∫ x, ∏ j, v j x ^ γ j ∂μ := by
    simp_rw [← heq]
    rw [integral_toReal hP (ae_lt_top' hP hPfin)]
    exact (ENNReal.ofReal_le_iff_le_toReal hPfin).mp hnear
  have HR := H ε he hε μ v (fun _ _ => ENNReal.toReal_nonneg) hi hn' hlower
  intro i
  constructor
  · rw [l1DensityError_eq_ofReal_integral _ (hu i) hP (hv i) hPfin]
    simp_rw [heq]
    exact ENNReal.ofReal_le_ofReal (HR i).1
  · intro j
    rw [l1DensityError_eq_ofReal_integral _ (hu i) (hu j) (hv i) (hv j)]
    exact ENNReal.ofReal_le_ofReal ((HR i).2 j)
end LpGowers
