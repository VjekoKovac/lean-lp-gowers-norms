module

public import LpGowers.EisnerTaoReduction
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Reduction of the ordinary inverse theorem to inverse Young

The nonnegative part of Eisner–Tao, arXiv:1012.3509, §6, only needs their
inverse Young estimate with two identical inputs. We integrate in the first
increment after applying the ordinary Lebesgue estimate to multiplicative
differences. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

private theorem cubeProduct_difference {G : Type*} [AddCommGroup G] (k : ℕ)
    (f : G → ℝ≥0) (a : G) (h : Fin k → G) (x : G) :
    cubeProduct k (fun y => f y * f (y+a)) h x =
      cubeProduct k f h x * cubeProduct k f h (x+a) := by
  induction k generalizing x with
  | zero => simp [cubeProduct]
  | succ k ih =>
      simp only [cubeProduct, ih, add_right_comm x (h 0) a]
      ac_rfl

/-- The single-coordinate Young moment which dominates the ordinary Gowers
quantity of order `k+1`. Both sides may be infinite. -/
theorem ordinary_moment_le_diagonal_young {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (k : ℕ) (hk : 1 ≤ k) {f : G → ℝ≥0} (hf : AEMeasurable f μ) :
    (ordinaryGowers μ (k+1) f) ^ (2^(k+1) : ℕ) ≤
      ∫⁻ a, (∫⁻ x, ((↑(f x ^ criticalExponent k 1) : ℝ≥0∞) *
        ↑(f (x+a) ^ criticalExponent k 1)) ∂μ) ^ ((k:ℝ)+1) ∂μ := by
  let r := criticalExponent k 1
  have hr : 0 < r := by dsimp [r,criticalExponent]; positivity
  let H := fun a x => f x * f (x+a)
  have hH (a) : AEMeasurable (H a) μ :=
    hf.mul (hf.comp_quasiMeasurePreserving (measurePreserving_add_right μ a).quasiMeasurePreserving)
  have hUk (a) : ordinaryGowers μ k (H a) ≤ lp μ r (liftNN (H a)) := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hks
    · have hr1 : r = 1 := by norm_num [r,criticalExponent]
      rw [hr1]
      exact (gowers_one_one μ (hH a)).le
    · have hB : lowerEndpoint k ≤ 1 := (lowerEndpoint_parameters (k := k-1) (by omega)).2.2.1
        |> (by simpa [Nat.sub_add_cancel hk] using ·)
      exact lebesgue_bound μ k hks  hB (hH a)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => G) 0
  let : SigmaFinite (cubeMeasure μ k) := by unfold cubeMeasure; infer_instance
  have he : MeasurePreserving e (cubeMeasure μ (k+1)) (μ.prod (cubeMeasure μ k)) :=
    measurePreserving_piFinSuccAbove _ 0
  have hm := measurable_autocorrelation_of_aemeasurable μ (k+1) hf
  have heq : (ordinaryGowers μ (k+1) f) ^ (2^(k+1) : ℕ) =
      ∫⁻ h, autocorrelation μ (k+1) f h ∂cubeMeasure μ (k+1) := by
    simp only [ordinaryGowers,gowers,lp,div_one,ENNReal.rpow_one,one_div]
    rw [← ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.rpow_inv_rpow (by positivity) _
  rw [heq, ← ((MeasurePreserving.symm e he).lintegral_comp hm),
    lintegral_prod (fun z => autocorrelation μ (k+1) f (e.symm z)) (hm.comp e.symm.measurable).aemeasurable]
  apply lintegral_mono
  intro a
  have heR (h : Fin k → G) :
      autocorrelation μ (k+1) f (e.symm (a,h)) = autocorrelation μ k (H a) h := by
    apply lintegral_congr
    intro x
    change cubeProduct (k+1) f ((0 : Fin (k+1)).insertNth a h) x = _
    rw [cubeProduct_insertNth, ← cubeProduct_difference]
  simp_rw [heR]
  have he' : (ordinaryGowers μ k (H a))^(2^k : ℕ) =
      ∫⁻ h, autocorrelation μ k (H a) h ∂cubeMeasure μ k := by
    simp only [ordinaryGowers,gowers,lp,div_one,ENNReal.rpow_one,one_div]
    rw [← ENNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.rpow_inv_rpow (by positivity) _
  rw [← he']
  refine (pow_le_pow_left' (hUk a) _).trans_eq ?_
  have harith : (1/r)*(2:ℝ)^k = (k:ℝ)+1 := by
    dsimp [r,criticalExponent]; field_simp
  simp only [lp,liftNN,H,ENNReal.coe_mul, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ← ENNReal.rpow_natCast, Nat.cast_pow,Nat.cast_ofNat, ← ENNReal.rpow_mul,harith,
    ENNReal.coe_rpow_of_nonneg _ hr.le, r]

/-- The identical-input inverse Young principle for the integer output
exponents needed here. The hypothesis is on the raw autocorrelation moment,
so the tolerated deficit is measured before taking roots. -/
def DiagonalInverseYoung.{u} : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
      (f : G → ℝ≥0), AEMeasurable f μ →
      let s := 2*(d:ℝ)/(d+1)
      (∫⁻ x, (f x : ℝ≥0∞)^s ∂μ) = 1 →
      ENNReal.ofReal (1-δ) ≤ ∫⁻ a, (∫⁻ x, (f x : ℝ≥0∞)*f (x+a) ∂μ)^(d:ℝ) ∂μ →
      ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
        lpDist μ s f (cosetProfile μ s 1 H x₀) ≤ ENNReal.ofReal η

/-- The proof of §6 in Eisner–Tao specialized to real nonnegative inputs.
No inverse result for polynomial phases is required. -/
theorem ordinaryInverse_of_diagonalInverseYoung.{u} (hY : DiagonalInverseYoung.{u}) :
    OrdinaryGowersInverse.{u} := by
  intro d hd η hη
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hk : 1 ≤ k := by omega
  let t := criticalExponent k 1
  let s := (2 : ℝ) * (k+1:ℕ) / ((k+1:ℕ)+1)
  let γ := 1/t
  let P : ℝ := 2^(k+1)
  have ht : 0 < t := by dsimp [t,criticalExponent]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hγ : 0 < γ := one_div_pos.mpr ht
  have hP : 0 < P := by dsimp [P]; positivity
  have hqt : t * s = criticalExponent (k+1) 1 := by
    dsimp [t,s,criticalExponent]
    push_cast
    rw [pow_succ]
    field_simp
  have hqs : s/γ = criticalExponent (k+1) 1 := by
    rw [← hqt]; dsimp only [γ]; field_simp
  obtain ⟨τ,hτ,hpower⟩ := power_transfer_tolerance.{u} hs hγ hη
  obtain ⟨δ,hδ,hδ1,hclose⟩ := hY _ hd τ hτ
  let α := 1 - (1-δ)^(1/P)
  have hlow : 0 < 1-δ := sub_pos.mpr hδ1
  have hα : 0 < α := sub_pos.mpr (Real.rpow_lt_one hlow.le (by linarith) (one_div_pos.mpr hP))
  have hα1 : α < 1 := sub_lt_self _ (Real.rpow_pos_of_pos hlow _)
  refine ⟨α,hα,hα1,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf hmass hU
  let F := fun x => f x ^ t
  have hF : AEMeasurable F μ := hf.pow_const _
  have hFm : (∫⁻ x, (F x : ℝ≥0∞)^s ∂μ) = 1 := by
    simpa only [F, ENNReal.coe_rpow_of_nonneg _ ht.le, ← ENNReal.rpow_mul, hqt] using hmass
  have hx := ENNReal.rpow_le_rpow hU hP.le
  have haeq : (ENNReal.ofReal (1-α))^P = ENNReal.ofReal (1-δ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hα1.le) hP.le]
    congr 1
    dsimp [α]; rw [sub_sub_cancel, ← Real.rpow_mul hlow.le, one_div_mul_cancel hP.ne', Real.rpow_one]
  rw [haeq] at hx
  have hpow : (ordinaryGowers μ (k+1) f)^P = (ordinaryGowers μ (k+1) f)^(2^(k+1):ℕ) := by
    rw [← ENNReal.rpow_natCast]; congr 1; push_cast; rfl
  rw [hpow] at hx
  have hcor := hx.trans (ordinary_moment_le_diagonal_young μ k hk hf)
  have hcor' : ENNReal.ofReal (1-δ) ≤ ∫⁻ a, (∫⁻ x, (F x : ℝ≥0∞)*F (x+a) ∂μ)^(↑(k+1):ℝ) ∂μ := by
    simpa only [F,t,Nat.cast_add,Nat.cast_one] using hcor
  obtain ⟨H,x₀,hc,ho,herr⟩ := hclose G μ F hF hFm hcor'
  let V := cosetProfile μ s 1 H x₀
  have hV : AEMeasurable V μ := by
    apply Measurable.aemeasurable
    classical
    exact Measurable.ite ((measurable_id.sub_const x₀) ho.measurableSet) measurable_const measurable_const
  have hdist := hpower G μ F V hF hV hFm (cosetProfile_unit_moment μ s hs H x₀ hc ho) herr
  have hID : (fun x => F x ^ γ) = f := by
    funext x; simp [F,γ,← NNReal.rpow_mul,ht.ne']
  change lpDist μ (s/γ) (fun x => F x ^ γ) (fun x => cosetProfile μ s 1 H x₀ x ^ γ) ≤ _ at hdist
  rw [hID, cosetProfile_unit_rpow μ s γ hs hγ H x₀ hc ho, hqs] at hdist
  exact ⟨H,x₀,hc,ho,hdist⟩

end LpGowers
