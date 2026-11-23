module

public import LpGowers.ThreeMoments
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Apply Lemma 6.2 to extended nonnegative functions using the
almost-everywhere finite representative obtained from a finite positive moment. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LpGowers

private theorem ofReal_abs_sub_toReal (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ENNReal.ofReal |a.toReal-b.toReal| = (a-b)+(b-a) := by
  rcases le_total b a with h | h
  · rw [tsub_eq_zero_of_le h, add_zero, abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono ha h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hb h)),
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb, ENNReal.ofReal_toReal ha]

/-- Three subunit moments close to one force proximity to a common
indicator, simultaneously at every intermediate power. -/
theorem three_moments_near_ennreal {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c)
    {η : ℝ} (hη : 0<η) : ∃ δ : ℝ, 0<δ ∧
    ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (F : X → ℝ≥0∞), Measurable F →
    (∀ t ∈ ({a,b,c} : Set ℝ), ENNReal.ofReal (1-δ) ≤ ∫⁻ x, (F x)^t ∂μ ∧
      (∫⁻ x,(F x)^t ∂μ) ≤ 1) →
    ∃ E : Set X, MeasurableSet E ∧ μ E ≠ ⊤ ∧ |μ.real E - 1| ≤ η ∧
      ∀ t ∈ Set.Icc a c,
        (∫⁻ x, ((F x - E.indicator 1 x) + (E.indicator 1 x - F x))^t ∂μ) ≤ ENNReal.ofReal η := by
  obtain ⟨δ,hd,H⟩ := three_moments_near ha hab hbc hη
  let ε := δ/2
  have he : 0 < ε := half_pos hd
  refine ⟨ε,he,?_⟩
  intro X _ μ F hF hm
  let V := fun x => (F x).toReal
  have mm (t : ℝ) : AEMeasurable (fun x => (F x)^t) μ := (hF.pow_const t).aemeasurable
  have hfin t (ht : t ∈ ({a,b,c} : Set ℝ)) : (∫⁻x, (F x)^t ∂μ) ≠ ⊤ :=
    ((hm t ht).2.trans_lt ENNReal.one_lt_top).ne
  have hr (t : ℝ) (ht : t ∈ ({a,b,c} : Set ℝ)) :
      Integrable (fun x => V x ^ t) μ ∧ |(∫ x,V x ^ t ∂μ)-1| ≤ ε := by
    simp only [V, ENNReal.toReal_rpow]
    refine ⟨integrable_toReal_of_lintegral_ne_top (mm t) (hfin t ht),?_⟩
    rw [integral_toReal (mm t) (ae_lt_top' (mm t) (hfin t ht))]
    have hlo := (ENNReal.ofReal_le_iff_le_toReal (hfin t ht)).mp (hm t ht).1
    have hhi : (∫⁻ x,(F x)^t ∂μ).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hm t ht).2
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hE,hmE,hEvol,herr⟩ := H ε he.le (half_lt_self hd) μ V hF.ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg) hr
  let E := {x | 1/2 < V x}
  refine ⟨E,hE,hmE.ne,hEvol,?_⟩
  intro t ht
  obtain ⟨hI,hbound⟩ := herr t ht
  have hn (x : X) : 0 ≤ |V x-E.indicator 1 x|^t := Real.rpow_nonneg (abs_nonneg _) _
  have eq := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hn)
  have hFfin : ∀ᵐ x ∂μ, F x ≠ ⊤ := by
    filter_upwards [ae_lt_top' (mm a) (hfin a (by simp))] with x hx hx'
    simp [hx',ENNReal.top_rpow_of_pos ha] at hx
  calc
    _ = ∫⁻ x, ENNReal.ofReal (|V x-E.indicator 1 x|^t) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hFfin] with x hx
      let y := E.indicator (1 : X → ℝ≥0∞) x
      have hy : y ≠ ⊤ := by classical by_cases h : x ∈ E <;> simp [y,h]
      have he' : y.toReal = E.indicator (1 : X → ℝ) x := by classical by_cases h : x ∈ E <;> simp [y,h]
      rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (ha.le.trans ht.1)]
      rw [← he', show V x = (F x).toReal by rfl, ofReal_abs_sub_toReal _ _ hx hy]
    _ ≤ ENNReal.ofReal η := eq.ge.trans (ENNReal.ofReal_le_ofReal hbound)

end LpGowers
