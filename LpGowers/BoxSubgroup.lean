module

public import LpGowers.BoxErrorDefs
public import LpGowers.SliceNorm
public import LpGowers.RectangleSquare

/-! # From a two-dimensional box error to an almost-closed set

The combined error controls the first-power distance to the rectangle and
the cubic Gowers prefactor in diagonal leakage at the same time.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Pointwise
namespace LpGowers

/-- Convert a combined cube error to the separate estimates that enter
the two-dimensional additive closure argument. -/
theorem two_dimensional_box_estimates {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {g : G → ℝ≥0} (hg : AEMeasurable g μ) {A B : Set G}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAm : μ A ≤ 2) (hBm : μ B ≤ 2)
    (herr : boxError μ 2 g ![A,B] ≤ 1) :
    l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 g)
      (fun h => (A×ˢB).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1)) ≤ boxError μ 2 g ![A,B] ∧
      (ordinaryGowers μ 3 g)^2 ≤ 2 := by
  classical
  let Q := Set.univ.pi ![A,B]
  let I := Q.indicator (1 : (Fin 2 → G) → ℝ≥0∞)
  let R := autocorrelation μ 2 g
  let D := fun h => (R h-I h)+(I h-R h)
  have qMem (h : Fin 2 → G) : h ∈ Q ↔ (h 0,h 1) ∈ A×ˢB := by
    simp [Q,Fin.forall_fin_succ,Set.mem_prod]
  have hArgs : ∀ i : Fin 2, MeasurableSet (![A,B] i) := by
    intro i; fin_cases i <;> simp [hA,hB]
  have hI : Measurable I := measurable_one.indicator (MeasurableSet.univ_pi hArgs)
  have ID (h : Fin 2 → G) :
      (A×ˢB).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1) = I h := by
    simp only [I,Set.indicator_apply,Pi.one_apply,qMem]
  have im : (∫⁻ h, I h ^ 2 ∂cubeMeasure μ 2) = μ A*μ B := by
    have hQ : MeasurableSet Q := MeasurableSet.univ_pi hArgs
    have point (h : Fin 2 → G) : I h ^ 2 = I h := by by_cases hq : h ∈ Q <;> simp [I,hq]
    simp_rw [point]
    rw [lintegral_indicator_one hQ,show cubeMeasure μ 2 Q = ∏ i : Fin 2, μ (![A,B] i) from
      Measure.pi_pi (fun _ => μ) ![A,B]]
    simp [Fin.prod_univ_two]
  constructor
  · unfold l1DensityError
    simp_rw [ID]
    exact lintegral_mono (fun h => (le_self_add : D h ≤ boxErrorAt (R h) (I h)))
  · apply slice_gowers_three_bound μ hg hI
    · rw [im]
      exact (mul_le_mul' hAm hBm).trans_eq (by norm_num)
    · exact (lintegral_mono (fun h => (le_add_self : D h^2 ≤ boxErrorAt (R h) (I h)))).trans herr

/-- The uniform two-dimensional box criterion for a compact open subgroup,
using exactly the two errors and the squared mass bound from slice selection. -/
theorem compact_open_of_boxError.{u} :
    ∃ η : ℝ, 0<η ∧ η<1 ∧
      ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0),
      AEMeasurable f μ → ∀ (A B : Set G), MeasurableSet A → MeasurableSet B →
      ENNReal.ofReal (1-η) ≤ μ A → μ A ≤ ENNReal.ofReal (1+η) →
      ENNReal.ofReal (1-η) ≤ μ B → μ B ≤ ENNReal.ofReal (1+η) →
      (∫⁻ x, liftNN f x ∂μ)^2 ≤ ENNReal.ofReal (1+η) →
      boxError μ 2 f ![A,B] ≤ ENNReal.ofReal η →
      ∃ H : AddSubgroup G, IsCompact (H : Set G) ∧ IsOpen (H : Set G) := by
  let η : ℝ := 1/10^12
  let t : ℝ≥0∞ := 1/10^12
  have hp : 0 < η := by norm_num [η]
  have hlt : η < 1 := by norm_num [η]
  have hc : ENNReal.ofReal η = t := by
    dsimp [η,t]
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have hlo : ENNReal.ofReal (1-η) = 1-t := by
    rw [ENNReal.ofReal_sub _ hp.le,ENNReal.ofReal_one,hc]
  have hhi : ENNReal.ofReal (1+η) = 1+t := by
    rw [ENNReal.ofReal_add (by norm_num) hp.le,ENNReal.ofReal_one,hc]
  have ht : t ≤ 1 := by rw [← hc,← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlt.le
  have h2 : 1+t ≤ 2 := (add_le_add_right ht 1).trans_eq (by norm_num)
  refine ⟨η,hp,hlt,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf A B hA hB ha₀ ha₁ hb₀ hb₁ hmass hbox
  rw [hlo] at ha₀ hb₀
  rw [hhi] at ha₁ hb₁ hmass
  rw [hc] at hbox
  have m : (∫⁻ x, liftNN f x ∂μ) ≤ 1+t := by
    by_cases h : (∫⁻ x, liftNN f x ∂μ) ≤ 1
    · exact h.trans le_self_add
    · exact (le_self_pow (le_of_not_ge h) (by decide : 2 ≠ 0)).trans hmass
  have ⟨hL,hU⟩ := two_dimensional_box_estimates μ hf hA hB (ha₁.trans h2)
    (hb₁.trans h2) (hbox.trans ht)
  exact compact_open_of_rectangle μ hf hA hB ha₀ ha₁ hb₀ hb₁ m (hL.trans hbox) hU

end LpGowers
