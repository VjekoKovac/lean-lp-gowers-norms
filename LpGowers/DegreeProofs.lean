module

public import LpGowers.Degree
public import Mathlib.MeasureTheory.Group.LIntegral

/-! # Autocorrelation marginals and the degree-lowering endpoint

The identities use Tonelli's theorem and translation invariance of Haar measure,
following equations (2.1)–(2.2) of Kovač and Rogers. -/

@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

section Measurability
variable {G X : Type*} [MeasurableSpace G] [AddCommMonoid G] [MeasurableAdd₂ G]
  [MeasurableSpace X] {f : G → ℝ≥0}

/-- Joint measurability, allowing the base point and all increments to depend
on an arbitrary parameter. -/
theorem measurable_cubeProduct_comp (hf : Measurable f) (k : ℕ)
    (h : Fin k → X → G) (hh : ∀ i, Measurable (h i)) (x : X → G) (hx : Measurable x) :
    Measurable (fun t => cubeProduct k f (fun i => h i t) (x t)) := by
  induction k generalizing x with
  | zero => exact measurable_coe_nnreal_ennreal.comp (hf.comp hx)
  | succ k ih =>
    exact (ih (fun i => h i.succ) (fun i => hh i.succ) x hx).mul
      (ih (fun i => h i.succ) (fun i => hh i.succ) (fun t => x t + h 0 t) (hx.add (hh 0)))

/-- Ordinary measurability of the multiple autocorrelation of a Borel representative. -/
theorem measurable_autocorrelation (μ : Measure G) [SFinite μ] (k : ℕ)
    (hf : Measurable f) : Measurable (autocorrelation μ k f) := by
  apply Measurable.lintegral_prod_right
  exact measurable_cubeProduct_comp hf k
    (fun i (t : (Fin k → G) × G) => t.1 i)
    (fun i => (measurable_pi_apply i).comp measurable_fst) _ measurable_snd
end Measurability

section Haar
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [μ.IsAddLeftInvariant] {f g : G → ℝ≥0}

/-- A null change of `f` changes the cube integrand only on a null set in
its base point for each *fixed* tuple of increments. -/
theorem cubeProduct_congr_ae (hfg : f =ᵐ[μ] g) (k : ℕ) (h : Fin k → G) :
    cubeProduct k f h =ᵐ[μ] cubeProduct k g h := by
  induction k with
  | zero => exact hfg.fun_comp (fun v : ℝ≥0 => (v : ℝ≥0∞))
  | succ k ih =>
    have e := ih (Fin.tail h)
    exact e.mul ((measurePreserving_add_right μ (h 0)).quasiMeasurePreserving.ae_eq_comp e)

/-- Every fixed increment tuple has the same correlation for a.e.-equal inputs. -/
theorem autocorrelation_congr_ae (hfg : f =ᵐ[μ] g) (k : ℕ) :
    autocorrelation μ k f = autocorrelation μ k g := by
  funext h
  exact lintegral_congr_ae (cubeProduct_congr_ae μ hfg k h)

/-- Even for a function measurable only in the completion the defining base-point
integral gives a genuinely measurable function of all increments. -/
theorem measurable_autocorrelation_of_aemeasurable [SFinite μ] (k : ℕ)
    (hf : AEMeasurable f μ) : Measurable (autocorrelation μ k f) := by
  rw [autocorrelation_congr_ae μ hf.ae_eq_mk k]
  exact measurable_autocorrelation μ k hf.measurable_mk
end Haar

private theorem cubeProduct_cons {G : Type*} [AddCommMonoid G] (k : ℕ)
    (f : G → ℝ≥0) (a : G) (h : Fin k → G) (x : G) :
    cubeProduct (k + 1) f (Fin.cons a h) x =
      cubeProduct k f h x * cubeProduct k f h (x + a) := by
  simp only [cubeProduct, Fin.tail_cons, Fin.cons_zero]

/-- Split all vertices by an arbitrary distinguished increment. -/
theorem cubeProduct_insertNth {G : Type*} [AddCommMonoid G] (k : ℕ)
    (f : G → ℝ≥0) (i : Fin (k + 1)) (a : G) (h : Fin k → G) (x : G) :
    cubeProduct (k + 1) f (i.insertNth (α := fun _ => G) a h) x =
      cubeProduct k f h x * cubeProduct k f h (x + a) := by
  induction k generalizing x with
  | zero =>
    have hi : i = 0 := Fin.eq_zero _
    subst i
    simp [cubeProduct]
  | succ k ih =>
    cases i using Fin.cases with
    | zero => simp only [Fin.insertNth_zero', cubeProduct, Fin.tail_cons, Fin.cons_zero]
    | succ i =>
      obtain ⟨b, t, rfl⟩ := Fin.exists_cons h
      simp only [Fin.insertNth_succ_cons, cubeProduct_cons]
      rw [ih i t x, ih i t (x + b), add_right_comm x b a]
      ac_rfl

section Marginal
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]

/-- Equation (2.1). This pointwise identity holds at every fixed tuple of the
remaining increments, even if its value is infinite. -/
theorem autocorrelation_marginal {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (k : ℕ) (i : Fin (k + 1)) (h : Fin k → G) :
    (∫⁻ a, autocorrelation μ (k + 1) f (i.insertNth (α := fun _ => G) a h) ∂μ) =
      (autocorrelation μ k f h) ^ (2 : ℕ) := by
  rw [autocorrelation_congr_ae μ hf.ae_eq_mk, autocorrelation_congr_ae μ hf.ae_eq_mk]
  let u := cubeProduct k (hf.mk f) h
  have hu : Measurable u := measurable_cubeProduct_comp hf.measurable_mk k
    (fun i (_ : G) => h i) (fun _ => measurable_const) id measurable_id
  simp only [autocorrelation, cubeProduct_insertNth]
  change (∫⁻ a, ∫⁻ x, u x * u (x + a) ∂μ ∂μ) = (∫⁻ x, u x ∂μ) ^ (2 : ℕ)
  rw [lintegral_lintegral_swap]
  · calc
      _ = ∫⁻ x, u x * (∫⁻ a, u a ∂μ) ∂μ := by
        apply lintegral_congr
        intro x
        rw [lintegral_const_mul (μ := μ) (f := fun a => u (x+a)) (u x)
          (hu.comp (measurable_const.add measurable_id))]
        rw [lintegral_add_left_eq_self]
      _ = _ := by rw [lintegral_mul_const _ hu, pow_two]
  · exact ((hu.comp measurable_snd).mul (hu.comp (measurable_snd.add measurable_fst))).aemeasurable
end Marginal

/-- Integrating the marginal identity over the remaining increments gives
the integral identity behind the endpoint of both degree-lowering families. -/
theorem lintegral_autocorrelation_succ {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) :
    (∫⁻ h, autocorrelation μ (k + 1) f h ∂cubeMeasure μ (k + 1)) =
      ∫⁻ h, (autocorrelation μ k f h) ^ (2 : ℕ) ∂cubeMeasure μ k := by
  let : SigmaFinite (cubeMeasure μ k) := by unfold cubeMeasure; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => G) 0
  have he : MeasurePreserving e (cubeMeasure μ (k + 1)) (μ.prod (cubeMeasure μ k)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) 0
  have hR := measurable_autocorrelation_of_aemeasurable μ (k + 1) hf
  calc
    _ = ∫⁻ z, autocorrelation μ (k + 1) f (e.symm z) ∂(μ.prod (cubeMeasure μ k)) :=
      ((MeasurePreserving.symm e he).lintegral_comp hR).symm
    _ = ∫⁻ h, ∫⁻ a, autocorrelation μ (k + 1) f (e.symm (a, h)) ∂μ ∂cubeMeasure μ k :=
      lintegral_prod_symm' _ (hR.comp e.symm.measurable)
    _ = _ := lintegral_congr (fun h => autocorrelation_marginal μ hf k 0 h)

/-- Equation (2.2), for the nonnegative functions of the introductory theorems.
The values may be infinite. -/
theorem gowers_one_succ_eq_gowers_two {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) :
    gowers μ (k + 1) 1 f = gowers μ k 2 f := by
  simp only [gowers, lp, ENNReal.rpow_one, div_one, lintegral_autocorrelation_succ μ hf,
    ENNReal.rpow_two, ← ENNReal.rpow_mul]
  congr 1
  rw [pow_succ]
  ring

/-- Finite weighted product of powers with a common base, valid also at zero and infinity. -/
theorem prod_const_rpow_of_nonneg {ι : Type*} (x : ℝ≥0∞) (s : Finset ι)
    (θ : ι → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    (∏ i ∈ s, x ^ (θ i)) = x ^ (∑ i ∈ s, θ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ENNReal.rpow_add_of_nonneg]
    · exact hθ i
    · exact Finset.sum_nonneg (fun j _ => hθ j)

/-- The entire `p=1` case of Theorem 1.4(a), with exact equality. Relation
(1.9) forces every lower exponent to equal 2. -/
theorem degree_forward_endpoint {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) (q θ : Fin (k + 1) → ℝ)
    (h : DegreeParameters k 1 q θ) (hθ : DegreeForward 1 θ) :
    gowers μ (k + 1) 1 f = lowerProduct μ k q θ f := by
  obtain ⟨hq, hsum, hrel⟩ := h
  obtain ⟨_, _, hpos⟩ := hθ
  have hq2 (i : Fin (k + 1)) : q i = 2 := by
    have he := hrel i
    simp only [div_one, sub_self, zero_div] at he
    have he' := (mul_eq_zero.mp he.symm).resolve_left (hpos i).ne'
    field_simp [(hq i).ne'] at he'
    norm_num at he'
    linarith
  simp only [gowers_one_succ_eq_gowers_two μ hf, lowerProduct, hq2]
  rw [prod_const_rpow_of_nonneg _ _ _ (fun i => (hpos i).le), hsum, ENNReal.rpow_one]

end LpGowers
