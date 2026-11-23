module

public import LpGowers.EuclideanInverse
public import LpGowers.YoungScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Strong continuity of the diagonal convolution moment

Minkowski preserves the unit mass in a strong limit. Applying the mixed
Young estimate in both orders gives continuity of the last sharp Young
objective at every real exponent greater than one.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

private theorem lpDist_swap {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ)
    (f g : X → ℝ≥0) : lpDist μ q f g = lpDist μ q g f := by
  simp only [lpDist, edist_comm (f _) (g _)]

private theorem lpDist_zero_input {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ)
    (f : X → ℝ≥0) : lpDist μ q f (fun _ => 0) = lp μ q (liftNN f) := by
  change lp μ q (fun x => edist (f x) (0 : ℝ≥0)) = lp μ q (fun x => (f x : ℝ≥0∞))
  simp [edist_dist, NNReal.dist_eq]

theorem unit_mass_of_lpDist_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {q : ℝ} (hq : 1 ≤ q) {f : ℕ → X → ℝ≥0} {g : X → ℝ≥0}
    (hf : ∀ j, AEMeasurable (f j) μ) (hg : AEMeasurable g μ)
    (hm : ∀ j, ∫⁻ x, (f j x : ℝ≥0∞) ^ q ∂μ = 1)
    (hD : Tendsto (fun j => lpDist μ q (f j) g) atTop (𝓝 0)) :
    ∫⁻ x, (g x : ℝ≥0∞) ^ q ∂μ = 1 := by
  have unit j : lp μ q (liftNN (f j)) = 1 := by simp [lp, liftNN, hm j]
  have hz : AEMeasurable (fun _ : X => (0:ℝ≥0)) μ := aemeasurable_const
  have upper j := lpDist_triangle μ hq g (f j) _ hg (hf j) hz
  simp_rw [lpDist_zero_input, unit, lpDist_swap μ q g] at upper
  have lower j := lpDist_triangle μ hq (f j) g _ (hf j) hg hz
  simp_rw [lpDist_zero_input, unit] at lower
  have u : lp μ q (liftNN g) ≤ 1 := by
    simpa using le_of_tendsto_of_tendsto' tendsto_const_nhds
      (hD.add (tendsto_const_nhds (x := (1:ℝ≥0∞)))) upper
  have l : 1 ≤ lp μ q (liftNN g) := by
    simpa using le_of_tendsto_of_tendsto' tendsto_const_nhds
      (hD.add (tendsto_const_nhds (x := lp μ q (liftNN g)))) lower
  have h := congrArg (· ^ q) (le_antisymm u l)
  simpa only [lp,liftNN, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith : q ≠ 0),
    ENNReal.rpow_one, ENNReal.one_rpow] using h

theorem youngMoment_tendsto_of_lpDist (n : ℕ) {s : ℝ} (hs : 1 < s)
    {f : ℕ → Rn n → ℝ≥0} {g : Rn n → ℝ≥0}
    (hf : ∀ j, AEMeasurable (f j) (euclideanMeasure n)) (hg : AEMeasurable g (euclideanMeasure n))
    (hm : ∀ j, ∫⁻ x, (f j x : ℝ≥0∞) ^ criticalExponent 1 s ∂euclideanMeasure n = 1)
    (hD : Tendsto (fun j => lpDist (euclideanMeasure n) (criticalExponent 1 s) (f j) g)
      atTop (𝓝 0)) : Tendsto (fun j => cubeMoment 1 n s (f j)) atTop (𝓝 (cubeMoment 1 n s g)) := by
  let μ := euclideanMeasure n
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  let q := 2*s/(s+1)
  have hq : criticalExponent 1 s = q := by simp [criticalExponent, q, add_comm]
  rw [hq] at hm hD
  have hqu : 1 ≤ q := (le_div_iff₀ (show 0 < s+1 by linarith)).2 (by linarith)
  have hgm := unit_mass_of_lpDist_tendsto μ hqu hf hg hm hD
  let N := fun (F : Rn n → ℝ≥0) => lp μ s (fun a => ∫⁻ x, (F x:ℝ≥0∞) * F (x+a) ∂μ)
  let E := fun j => lpDist μ q (f j) g + lpDist μ q (f j) g
  have e : Tendsto E atTop (𝓝 0) := by simpa [E] using hD.add hD
  have upper j : N (f j) ≤ N g + E j := by
    change N (f j) ≤ N g + (lpDist μ q (f j) g + lpDist μ q (f j) g)
    rw [← two_mul]
    exact diagonalYoung_lp_le_real μ s hs (f j) g (hf j) hg (hm j) hgm
  have lower j : N g - E j ≤ N (f j) := by
    apply tsub_le_iff_right.2
    change N g ≤ N (f j) + (lpDist μ q (f j) g + lpDist μ q (f j) g)
    rw [← two_mul, lpDist_swap μ q (f j) g]
    exact diagonalYoung_lp_le_real μ s hs g (f j) hg (hf j) hgm (hm j)
  have tn : Tendsto (fun j => N (f j)) atTop (𝓝 (N g)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ lower upper
    · simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := N g)) e (Or.inr ENNReal.zero_ne_top)
    · simpa using (tendsto_const_nhds (x := N g)).add e
  have power (F : Rn n → ℝ≥0) (hF : AEMeasurable F μ) : cubeMoment 1 n s F = N F ^ s := by
    rw [cubeMoment_one n s F hF]
    simp only [N, lp, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith : s ≠ 0), ENNReal.rpow_one, μ]
  rw [power g hg, show (fun j => cubeMoment 1 n s (f j)) = (fun j => N (f j) ^ s) from
    funext (fun j => power (f j) (hf j))]
  exact Filter.Tendsto.ennrpow_const s tn

end LpGowers
