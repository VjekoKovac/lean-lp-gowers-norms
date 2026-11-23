module

public import LpGowers.LebesgueProofs
public import LpGowers.LoomisWhitney
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Symmetric forward degree lowering

This is the symmetric adjoint Loomis–Whitney argument from §§2 and 5,
specialized to the exponents of the lower endpoint in §3. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace LpGowers

theorem measurable_omitCoord {G : Type*} [MeasurableSpace G] {k : ℕ}
    (i : Fin (k+1)) : Measurable (deleteCoord (X := G) i) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply (i.succAbove j))

private theorem omitCoord_insert {G : Type*} {k : ℕ} (i : Fin (k+1)) (a : G) (h : Fin k → G) :
    deleteCoord i (i.insertNth a h) = h := funext (fun j => by simp [deleteCoord])

theorem weighted_marginal {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] {k : ℕ} (i : Fin (k+1))
    {F : (Fin (k+1) → G) → ℝ≥0∞} {M W : (Fin k → G) → ℝ≥0∞}
    (hF : Measurable F) (hW : Measurable W)
    (hmarg : ∀ h, ∫⁻ a, F (i.insertNth a h) ∂μ = M h ^ (2 : ℕ)) :
    (∫⁻ x, F x * W (deleteCoord i x) ∂cubeMeasure μ (k+1)) =
      ∫⁻ y, M y ^ (2 : ℕ) * W y ∂cubeMeasure μ k := by
  let : SigmaFinite (cubeMeasure μ k) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => G) i
  have he : MeasurePreserving e (cubeMeasure μ (k+1)) (μ.prod (cubeMeasure μ k)) :=
    measurePreserving_piFinSuccAbove _ i
  let U := fun x => F x * W (deleteCoord i x)
  have hU : Measurable U := hF.mul (hW.comp (measurable_omitCoord i))
  calc
    _ = ∫⁻ z, U (e.symm z) ∂μ.prod (cubeMeasure μ k) :=
      ((MeasurePreserving.symm e he).lintegral_comp hU).symm
    _ = ∫⁻ y, ∫⁻ a, U (e.symm (a,y)) ∂μ ∂cubeMeasure μ k :=
      lintegral_prod_symm' _ (hU.comp e.symm.measurable)
    _ = _ := by
      apply lintegral_congr
      intro y
      change (∫⁻ a, F (i.insertNth a y) * W (deleteCoord i (i.insertNth a y)) ∂μ) = _
      simp_rw [omitCoord_insert]
      have hfy : Measurable (fun a => F (i.insertNth a y)) :=
        hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
      rw [lintegral_mul_const _ hfy, hmarg y]

theorem finite_marginal_on_support {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] {k : ℕ} (i : Fin (k+1))
    {F : (Fin (k+1) → G) → ℝ≥0∞} {M : (Fin k → G) → ℝ≥0∞}
    (hF : Measurable F) (hM : Measurable M) {q : ℝ} (hq : 0 < q)
    (hN : (∫⁻ y, M y ^ q ∂cubeMeasure μ k) ≠ ⊤)
    (hmarg : ∀ h, ∫⁻ a, F (i.insertNth a h) ∂μ = M h ^ (2 : ℕ)) :
    ∀ᵐ x ∂cubeMeasure μ (k+1), F x ≠ 0 → M (deleteCoord i x) ≠ 0 ∧ M (deleteCoord i x) ≠ ⊤ := by
  let W := fun y => if M y = 0 ∨ M y = ⊤ then (1 : ℝ≥0∞) else 0
  have hW : Measurable W := Measurable.ite
    ((measurableSet_eq_fun hM measurable_const).union (measurableSet_eq_fun hM measurable_const))
    measurable_const measurable_const
  have hP := weighted_marginal μ i hF hW hmarg
  have hZ : (∫⁻ y, M y ^ (2 : ℕ) * W y ∂cubeMeasure μ k) = 0 := by
    apply (lintegral_eq_zero_iff ((hM.pow_const (2 : ℕ)).mul hW)).mpr
    filter_upwards [ae_lt_top (hM.pow_const q) hN] with y hy
    have hn : M y ≠ ⊤ := by
      intro ht
      simp [ht, ENNReal.top_rpow_of_pos hq] at hy
    by_cases hz : M y = 0 <;> simp [W, hz, hn]
  have hAE := (lintegral_eq_zero_iff (hF.mul (hW.comp (measurable_omitCoord i)))).mp (hP.trans hZ)
  filter_upwards [hAE] with x hx hf
  by_contra! hbad
  have hb : M (deleteCoord i x) = 0 ∨ M (deleteCoord i x) = ⊤ := by tauto
  exact hf (by simpa [W, hb] using hx)

private theorem normFactor {k : ℕ} {a b p q r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hscale : a * ((k : ℝ) + 1) = p) (hcancel : (q * r) * b + (q - 2) * a = 0)
    (z : ℝ≥0∞) (m : Fin (k+1) → ℝ≥0∞) (hm : ∀ i, m i ≠ 0 ∧ m i ≠ ⊤) :
    (∏ i, (m i ^ q) ^ r) ^ b * (∏ i, (z * m i ^ (q - 2)) ^ a) = z ^ p := by
  rw [← ENNReal.prod_rpow_of_nonneg hb]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ i : Fin (k+1), z ^ a) = z ^ p := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_add, Nat.cast_one, hscale]
  rw [hprod, mul_left_comm, ← Finset.prod_mul_distrib]
  simp [← ENNReal.rpow_add _ _ (hm _).1 (hm _).2, hcancel]

/-- The symmetric adjoint Loomis–Whitney bound on the `p`-moment of a
joint density with identical square-root marginals. The formula is valid
when marginals vanish on a positive-measure set. -/
theorem symmetric_moment_lowering {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] (j : ℕ)
    {F : (Fin (j+2) → G) → ℝ≥0∞} {M : (Fin (j+1) → G) → ℝ≥0∞}
    (hF : Measurable F) (hM : Measurable M) {p q : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q)
    (hrel : q * (1 / ((j : ℝ) + 1)) * (1 - p) + (q - 2) * (p / ((j : ℝ) + 2)) = 0)
    (hmarg : ∀ i : Fin (j+2), ∀ h, ∫⁻ a, F (i.insertNth a h) ∂μ = M h ^ (2 : ℕ)) :
    (∫⁻ x, F x ^ p ∂cubeMeasure μ (j+2)) ≤
      (∫⁻ y, M y ^ q ∂cubeMeasure μ (j+1)) ^ (2 * p / q) := by
  let n : ℝ := j + 2
  let a := p / n
  let b := 1 - p
  let r := 1 / ((j : ℝ) + 1)
  let N := ∫⁻ y, M y ^ q ∂cubeMeasure μ (j+1)
  let A := fun (i : Fin (j+2)) x => F x * M (deleteCoord i x) ^ (q - 2)
  let B := fun x => ∏ i : Fin (j+2), (M (deleteCoord i x) ^ q) ^ r
  have hn : 0 < n := by dsimp [n]; positivity
  have ha : 0 ≤ a := div_nonneg hp.le hn.le
  have hb : 0 ≤ b := sub_nonneg.mpr hp1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscale : a * n = p := div_mul_cancel₀ _ hn.ne'
  have hplus : b + p = 1 := by dsimp [b]; ring
  have hcancel : (q * r) * b + (q - 2) * a = 0 := hrel
  have hfinal : r * n * b + a * n = 2 * p / q := by
    rw [eq_div_iff hq.ne']
    linear_combination n * hcancel + 2 * hscale
  have hA (i : Fin (j+2)) : Measurable (A i) :=
    hF.mul ((hM.comp (measurable_omitCoord i)).pow_const _)
  have hB : Measurable B := Finset.measurable_prod _ (fun i _ =>
    ((hM.comp (measurable_omitCoord i)).pow_const q).pow_const r)
  change _ ≤ N ^ (2 * p / q)
  by_cases ht : N = ⊤
  · rw [ht, ENNReal.top_rpow_of_pos (by positivity)]
    exact le_top
  have hm : ∀ᵐ x ∂cubeMeasure μ (j+2), ∀ i : Fin (j+2), F x ≠ 0 →
      M (deleteCoord i x) ≠ 0 ∧ M (deleteCoord i x) ≠ ⊤ :=
    ae_all_iff.mpr (fun i => finite_marginal_on_support μ i hF hM hq ht (hmarg i))
  have hfactors : ∀ᵐ x ∂cubeMeasure μ (j+2),
      F x ^ p ≤ B x ^ b * ∏ i, A i x ^ a := by
    filter_upwards [hm] with x hx
    by_cases hz : F x = 0
    · simp [hz, ENNReal.zero_rpow_of_pos hp]
    · apply le_of_eq
      exact (normFactor ha hb (by push_cast; dsimp [n] at hscale; linarith only [hscale])
        hcancel (F x) (fun i => M (deleteCoord i x)) (fun i => hx i hz)).symm
  have hAint (i : Fin (j+2)) : (∫⁻ x, A i x ∂cubeMeasure μ (j+2)) ≤ N := by
    change (∫⁻ x, F x * (fun h => M h ^ (q-2)) (deleteCoord i x) ∂_) ≤ N
    rw [weighted_marginal μ i hF (hM.pow_const (q-2)) (hmarg i)]
    apply lintegral_mono_ae
    filter_upwards [ae_lt_top (hM.pow_const q) ht] with y hy
    have hmt : M y ≠ ⊤ := by
      intro h
      simp [h, ENNReal.top_rpow_of_pos hq] at hy
    by_cases hm0 : M y = 0
    · simp [hm0, ENNReal.zero_rpow_of_pos hq]
    · rw [← ENNReal.rpow_two, ← ENNReal.rpow_add _ _ hm0 hmt]
      simp
  have hBint : (∫⁻ x, B x ∂cubeMeasure μ (j+2)) ≤ N ^ (r * n) := by
    have hlw := functionalLoomisWhitney μ j (fun _ h => M h ^ q) (fun _ => hM.pow_const q)
    change (∫⁻ x, B x ∂_) ≤ ∏ _ : Fin (j+2), N ^ r at hlw
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul, Nat.cast_add, Nat.cast_ofNat, n] using hlw
  have hweights : b + ∑ _ : Fin (j+2), a = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_ofNat]
    change b + n * a = 1
    rw [mul_comm n, hscale, hplus]
  have hh := ENNReal.lintegral_mul_prod_norm_pow_le (μ := cubeMeasure μ (j+2)) Finset.univ hB.aemeasurable
    (fun i _ => (hA i).aemeasurable) b hweights hb (fun _ _ => ha)
  calc
    _ ≤ _ := lintegral_mono_ae hfactors
    _ ≤ _ := hh
    _ ≤ (N ^ (r * n)) ^ b * ∏ _ : Fin (j+2), N ^ a := by
      exact mul_le_mul (ENNReal.rpow_le_rpow hBint hb)
        (Finset.prod_le_prod (fun i _ => ENNReal.rpow_le_rpow (hAint i) ha)) zero_le zero_le
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul, Nat.cast_add, Nat.cast_ofNat]
      change N ^ (r * n * b) * N ^ (a * n) = _
      rw [← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (mul_nonneg hr hn.le) hb)
        (mul_nonneg ha hn.le), hfinal]

section Haar

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]

/-- The forward estimate of Theorem 1.4(a) with all lower exponents equal
and all weights equal. The relation is written after clearing reciprocals. -/
theorem degree_symmetric (j : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q)
    (hrel : q * (1 / ((j : ℝ) + 1)) * (1 - p) + (q - 2) * (p / ((j : ℝ) + 2)) = 0)
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ (j+2) p f ≤ gowers μ (j+1) q f := by
  have h := symmetric_moment_lowering μ j
    (measurable_autocorrelation_of_aemeasurable μ (j+2) hf)
    (measurable_autocorrelation_of_aemeasurable μ (j+1) hf) hp hp1 hq hrel
    (autocorrelation_marginal μ hf (j+1))
  have hexp : 2 * p / q * (1 / p) * (1 / (2 : ℝ) ^ (j+2)) =
      (1 / q) * (1 / (2 : ℝ) ^ (j+1)) := by
    rw [pow_succ (2 : ℝ) (j+1)]
    field_simp
  unfold gowers lp
  have hr := ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow h (one_div_nonneg.mpr hp.le))
    (by positivity : 0 ≤ 1 / (2 : ℝ) ^ (j+2))
  simpa only [← ENNReal.rpow_mul, hexp] using hr

/-- Iterating symmetric lowering gives the closed `L¹` endpoint at every degree. -/
theorem lebesgue_lower_endpoint (d : ℕ) (hd : 1 ≤ d) {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) : gowers μ d (lowerEndpoint d) f ≤ lp μ 1 (liftNN f) := by
  induction d, hd using Nat.le_induction with
  | base =>
      rw [show lowerEndpoint 1 = 1 by norm_num [lowerEndpoint], gowers_one_one μ hf]
  | succ k hk ih =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      let p := lowerEndpoint (j+2)
      let q := lowerEndpoint (j+1)
      obtain ⟨⟨hqs,_,hrels⟩, hp, hp1, _⟩ := lowerEndpoint_parameters hk
      have hq : 0 < q := hqs 0
      have hK : (0 : ℝ) < j + 1 := by positivity
      have hK' : (0 : ℝ) < j + 2 := by positivity
      have hrel := hrels 0
      change (1 - 1 / p) / (↑(j+1) : ℝ) = (1 / ((↑(j+1) : ℝ) + 1)) * (1 - 2/q) at hrel
      have hcancel : q * (1 / ((j : ℝ) + 1)) * (1 - p) +
          (q - 2) * (p / ((j : ℝ) + 2)) = 0 := by
        push_cast at hrel
        rw [show (j : ℝ) + 1 + 1 = j + 2 by ring] at hrel
        have hp' : 0 < p := hp
        field_simp [hp'.ne', hq.ne', hK.ne', hK'.ne'] at hrel ⊢
        linear_combination -hrel
      exact (degree_symmetric μ j hp hp1 hq hcancel hf).trans ih

/-- The main Lebesgue inequality of Theorem 1.2(a), under the weaker assumptions
of a sigma-finite translation-invariant measure on a measurably additive group. -/
theorem lebesgue_bound (d : ℕ) (hd : 2 ≤ d) {p : ℝ} (hp : lowerEndpoint d ≤ p)
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    gowers μ d p f ≤ lp μ (criticalExponent d p) (liftNN f) := by
  have hend := fun F (hF : AEMeasurable F μ) =>
    lebesgue_lower_endpoint μ d (by omega) hF
  rcases hp.eq_or_lt with rfl | hlt
  · rw [criticalExponent_lowerEndpoint hd]
    exact hend f hf
  · exact lebesgue_bound_of_lower_endpoint μ hd hlt hf hend

end Haar

/-- Exact, unconditional statement of the first clause of Theorem 1.2. -/
theorem lebesgueBound.{u} : LebesgueBound.{u} := by
  intro d hd p hp G _ _ _ _ _ _ _ _ μ _ f hf
  exact lebesgue_bound μ d hd hp hf

end LpGowers
