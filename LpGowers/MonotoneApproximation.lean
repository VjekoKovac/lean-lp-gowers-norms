module

public import LpGowers.LebesgueProofs
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! The monotone passage to general inputs in §6. The truncations have
bounded amplitude and support of finite measure, for every Haar normalization. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

theorem cubeProduct_mono {G : Type*} [AddCommMonoid G] {f g : G → ℝ≥0} (hfg : f ≤ g)
    (d : ℕ) (h : Fin d → G) (x : G) : cubeProduct d f h x ≤ cubeProduct d g h x := by
  induction d generalizing x with
  | zero => exact ENNReal.coe_le_coe.mpr (hfg x)
  | succ d ih => exact mul_le_mul' (ih _ _) (ih _ _)

theorem gowers_mono {G : Type*} [AddCommMonoid G] [MeasurableSpace G]
    (μ : Measure G) {f g : G → ℝ≥0} (hfg : f ≤ g) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p f ≤ gowers μ d p g := by
  unfold gowers lp autocorrelation
  gcongr with h x
  exact cubeProduct_mono hfg d h x

private theorem sup_mul_mono (a b : ℕ → ℝ≥0∞) (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n) * (⨆ n, b n) = ⨆ n, a n * b n := by
  apply le_antisymm
  · rw [ENNReal.iSup_mul]
    refine iSup_le fun i => ?_
    rw [ENNReal.mul_iSup]
    exact iSup_le fun j => (mul_le_mul' (ha (le_max_left i j))
      (hb (le_max_right i j))).trans (le_iSup (fun n => a n * b n) (max i j))
  · exact iSup_le fun n => mul_le_mul' (le_iSup a n) (le_iSup b n)

private theorem cubeProduct_sup {G : Type*} [AddCommMonoid G] (f : G → ℝ≥0)
    (v : ℕ → G → ℝ≥0) (hv : Monotone v) (he : ∀ x, (f x : ℝ≥0∞) = ⨆ n, (v n x : ℝ≥0∞))
    (d : ℕ) (h : Fin d → G) (x : G) : cubeProduct d f h x = ⨆ n, cubeProduct d (v n) h x := by
  induction d generalizing x with
  | zero => exact he x
  | succ d ih =>
    simp only [cubeProduct, ih]
    exact sup_mul_mono _ _ (fun _ _ hle => cubeProduct_mono (hv hle) _ _ _)
      (fun _ _ hle => cubeProduct_mono (hv hle) _ _ _)

/-- Gowers functionals commute with increasing limits, even for 0 < p < 1
and when the limiting functional is infinite. -/
theorem gowers_monotone_convergence {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    (f : G → ℝ≥0) (v : ℕ → G → ℝ≥0) (hv : Monotone v)
    (hm : ∀ n, AEMeasurable (v n) μ)
    (he : ∀ x, (f x : ℝ≥0∞) = ⨆ n, (v n x : ℝ≥0∞)) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p f = ⨆ n, gowers μ d p (v n) := by
  have hmR : Monotone (fun n => autocorrelation μ d (v n)) :=
    fun _ _ hle h => lintegral_mono (cubeProduct_mono (hv hle) d h)
  have eqR (h) : autocorrelation μ d f h = ⨆ n, autocorrelation μ d (v n) h := by
    unfold autocorrelation
    simp_rw [cubeProduct_sup f v hv he d h]
    apply lintegral_iSup' (fun n => aemeasurable_cubeProduct_fixed μ (hm n) _ _)
    exact ae_of_all _ fun x _ _ hij => cubeProduct_mono (hv hij) d h x
  simp only [gowers,lp,eqR,ENNReal.iSup_rpow_of_pos hp]
  rw [lintegral_iSup (fun n => (measurable_autocorrelation_of_aemeasurable μ d (hm n)).pow_const p)
    (fun i j hij h => ENNReal.rpow_le_rpow (hmR hij h) hp.le),
    ENNReal.iSup_rpow_of_pos (one_div_pos.mpr hp), ENNReal.iSup_rpow_of_pos (by positivity)]

/-- Truncate in both amplitude and support along an increasing exhaustion. -/
def finiteTruncation {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (f : G → ℝ≥0) (n : ℕ) : G → ℝ≥0 :=
  (spanningSets μ n).indicator (fun x => min (f x) n)

theorem finiteTruncation_mono {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (f : G → ℝ≥0) : Monotone (finiteTruncation μ f) := by
  classical
  intro i j hij x
  by_cases hx : x ∈ spanningSets μ i
  · simp [finiteTruncation, hx, spanningSets_mono hij hx, Nat.cast_le.mpr hij]
  · simp [finiteTruncation,hx]

theorem finiteTruncation_sup {G : Type*} [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (f : G → ℝ≥0) (x : G) : (f x : ℝ≥0∞) = ⨆ n, (finiteTruncation μ f n x : ℝ≥0∞) := by
  classical
  obtain ⟨i,hi⟩ := Set.iUnion_eq_univ_iff.mp (iUnion_spanningSets μ) x
  obtain ⟨j,hj⟩ := exists_nat_ge (f x)
  have hx : x ∈ spanningSets μ (max i j) := spanningSets_mono (le_max_left _ _) hi
  have hb : f x ≤ (max i j : ℕ) := hj.trans (Nat.cast_le.mpr (le_max_right _ _))
  refine le_antisymm ?_ (iSup_le fun n => ?_)
  · exact le_iSup_of_le (max i j) (by simp only [finiteTruncation,Set.indicator_of_mem hx,min_eq_left hb]; exact le_rfl)
  · by_cases hh : x ∈ spanningSets μ n <;> simp [finiteTruncation,hh]

theorem aemeasurable_finiteTruncation {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] {f : G → ℝ≥0} (hf : AEMeasurable f μ) (n : ℕ) :
    AEMeasurable (finiteTruncation μ f n) μ :=
  (hf.min aemeasurable_const).indicator (measurableSet_spanningSets μ n)

/-- At every positive exponent the Gowers functional is the supremum of
its values on these bounded functions of finite-measure support. -/
theorem gowers_eq_iSup_finiteTruncation {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p f = ⨆ n, gowers μ d p (finiteTruncation μ f n) :=
  gowers_monotone_convergence μ f _ (finiteTruncation_mono μ f)
    (aemeasurable_finiteTruncation μ hf) (finiteTruncation_sup μ f) d hp

end LpGowers
