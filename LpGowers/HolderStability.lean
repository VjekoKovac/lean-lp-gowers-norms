module

public import LpGowers.MomentDeficit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Stability of multi-factor Hölder

Lemma 5.1 of Kovač–Rogers, in finite weighted form. The square of the distance
from each square root to the square root of the geometric mean is controlled
by the AM–GM deficit. Integration gives a uniform L¹ estimate.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LpGowers

private theorem weighted_sqrt_deficit {ι : Type*} [Fintype ι] (γ u : ι → ℝ)
    (hγ : ∀ i, 0 ≤ γ i) (hs : ∑ i, γ i = 1) (hu : ∀ i, 0 ≤ u i) :
    let g := ∏ i, u i ^ γ i
    ∀ i, γ i * (Real.sqrt (u i) - Real.sqrt g)^2 ≤ (∑ j, γ j * u j) - g := by
  classical
  intro g i
  have hg : 0 ≤ g := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu j) _
  have hsqrt : Real.sqrt g ≤ ∑ j, γ j * Real.sqrt (u j) := by
    have he (j : ι) : Real.sqrt (u j ^ γ j) = (Real.sqrt (u j)) ^ γ j := by
      simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul (hu j), mul_comm (γ j)]
    rw [show Real.sqrt g = ∏ j, (Real.sqrt (u j))^ γ j by
      dsimp [g]; rw [Real.sqrt_prod _ (fun j _ => Real.rpow_nonneg (hu j) _)]; simp only [he]]
    exact Real.geom_mean_le_arith_mean_weighted _ _ _ (fun j _ => hγ j) hs (fun j _ => Real.sqrt_nonneg _)
  have hsquares (j : ι) : γ j * (Real.sqrt (u j)-Real.sqrt g)^2 =
      γ j * u j + γ j*g - (2*Real.sqrt g)*(γ j*Real.sqrt (u j)) := by
    calc
      _ = γ j * (Real.sqrt (u j))^2 + γ j*(Real.sqrt g)^2 - (2*Real.sqrt g)*(γ j*Real.sqrt (u j)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hu j),Real.sq_sqrt hg]
  have hcross := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg g))
  calc
    _ ≤ ∑ j, γ j * (Real.sqrt (u j)-Real.sqrt g)^2 :=
      Finset.single_le_sum (f := fun j => γ j * (Real.sqrt (u j)-Real.sqrt g)^2)
        (fun j _ => mul_nonneg (hγ j) (sq_nonneg _)) (Finset.mem_univ i)
    _ = (∑ j, γ j * u j) + g - 2*Real.sqrt g * (∑ j, γ j * Real.sqrt (u j)) := by
      simp only [hsquares, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, hs, one_mul]
    _ ≤ _ := by nlinarith [Real.sq_sqrt hg]

private theorem root_trade {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (s : ℝ) :
    2*s * |A-B| ≤ (Real.sqrt A-Real.sqrt B)^2 + 2*s^2*(A+B) := by
  have prod : |A-B| = |Real.sqrt A-Real.sqrt B| * (Real.sqrt A+Real.sqrt B) := by
    rw [show A-B = (Real.sqrt A-Real.sqrt B)*(Real.sqrt A+Real.sqrt B) by
      nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB],abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))]
  have sumsq : (Real.sqrt A + Real.sqrt B)^2 ≤ 2*(A+B) := by
    nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB,sq_nonneg (Real.sqrt A-Real.sqrt B)]
  have trivial := sq_nonneg (|Real.sqrt A-Real.sqrt B|-s*(Real.sqrt A+Real.sqrt B))
  rw [prod]
  nlinarith [mul_le_mul_of_nonneg_left sumsq (sq_nonneg s),sq_abs (Real.sqrt A-Real.sqrt B)]

/-- Quantitative Hölder stability. For each normalized input density the L¹ gap
to the joint geometric mean satisfies this bound for every real scale λ. -/
theorem holder_stability_estimate {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hs : ∑ i, γ i = 1)
    (u : ι → X → ℝ) (hu : ∀ i x, 0 ≤ u i x) (hi : ∀ i, Integrable (u i) μ)
    (hn : ∀ i, (∫ x, u i x ∂μ) ≤ 1) (ε : ℝ)
    (hnear : 1-ε ≤ ∫ x, ∏ j, (u j x) ^ γ j ∂μ) (s : ℝ) (i : ι) :
    2*s * γ i * (∫ x, |u i x - ∏ j, (u j x)^γ j| ∂μ) ≤ ε + 4*s^2*γ i := by
  classical
  let S (x : X) := ∑ j, γ j * u j x
  let G (x : X) := ∏ j, (u j x) ^ γ j
  have hnG (x : X) : 0 ≤ G x := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu j x) _
  have hgs (x : X) : G x ≤ S x := Real.geom_mean_le_arith_mean_weighted _ _ _
    (fun j _ => (hγ j).le) hs (fun j _ => hu j x)
  have hS : Integrable S μ := integrable_finsetSum _ fun j _ => (hi j).const_mul _
  have hG : Integrable G μ := by
    apply hS.mono' (Finset.aemeasurable_fun_prod Finset.univ fun j _ => (hi j).aemeasurable.pow_const (γ j)).aestronglyMeasurable
    filter_upwards with x
    change ‖G x‖ ≤ S x
    rw [Real.norm_eq_abs,abs_of_nonneg (hnG x)]
    exact hgs x
  have hδ : Integrable (fun x => |u i x-G x|) μ := (hi i |>.sub hG).abs
  have hsum : (∫ x,S x ∂μ) ≤ 1 := by
    unfold S
    rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
    simp only [integral_const_mul]
    rw [← hs]
    exact Finset.sum_le_sum fun j _ => by simpa using mul_le_mul_of_nonneg_left (hn j) (hγ j).le
  have hG1 : (∫ x,G x ∂μ) ≤ 1 := (integral_mono hG hS hgs).trans hsum
  let K := 2 * s^2 * γ i
  have hk : 0 ≤ K := by dsimp [K]; positivity [hγ i]
  have hineq (x : X) : (2*s*γ i) * |u i x-G x| ≤ (S x-G x) + K*(u i x+G x) := by
    have h := weighted_sqrt_deficit γ (fun j => u j x) (fun j => (hγ j).le) hs (fun j => hu j x) i
    have ht := mul_le_mul_of_nonneg_left (root_trade (hu i x) (hnG x) s) (hγ i).le
    change γ i * (Real.sqrt (u i x)-Real.sqrt (G x))^2 ≤ S x-G x at h
    unfold K; linarith only [show 2*s*γ i*|u i x-G x| ≤ γ i*(Real.sqrt (u i x)-Real.sqrt (G x))^2 + 2*s^2*γ i*(u i x+G x) by linarith only [ht], h]
  have hp := integral_mono (hδ.const_mul (2*s*γ i))
      ((hS.sub hG).add (((hi i).add hG).const_mul K)) hineq
  simp only [integral_add' (hS.sub hG) (((hi i).add hG).const_mul K),
    integral_sub' hS hG,integral_const_mul,integral_add' (hi i) hG] at hp
  change 1-ε ≤ ∫ x,G x ∂μ at hnear
  change 2*s*γ i*(∫ x,|u i x-G x| ∂μ) ≤ _
  calc
    _ ≤ ((∫ x,S x ∂μ)-(∫ x,G x ∂μ))+K*((∫ x,u i x ∂μ)+(∫ x,G x ∂μ)) := hp
    _ ≤ (1-(∫ x,G x ∂μ))+K*(1+(∫ x,G x ∂μ)) :=
      add_le_add (sub_le_sub_right hsum _) (mul_le_mul_of_nonneg_left (add_le_add (hn i) le_rfl) hk)
    _ ≤ ε + K*2 := add_le_add (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hk)
    _ = _ := by dsimp [K]; ring

/-- Lemma 5.1, also allowing masses at most one. Nonnegative factors in a nearly extremal weighted
Hölder inequality are close in L¹ to each other and to their geometric mean.
The deficit threshold is independent of the measure space and the inputs. -/
theorem holder_stability {ι : Type*} [Fintype ι] [Nonempty ι] (γ : ι → ℝ)
    (hγ : ∀ i, 0 < γ i) (hs : ∑ i, γ i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : ι → X → ℝ),
    (∀ i x, 0 ≤ u i x) → (∀ i, Integrable (u i) μ) →
    (∀ i, (∫ x, u i x ∂μ) ≤ 1) →
    (1-ε ≤ ∫ x, ∏ j, (u j x) ^ γ j ∂μ) → ∀ i,
    (∫ x, |u i x - ∏ j, (u j x)^γ j| ∂μ) ≤ η ∧
      ∀ j, (∫ x, |u i x - u j x| ∂μ) ≤ η := by
  classical
  obtain ⟨j, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι) γ Finset.univ_nonempty
  refine ⟨(η^2/64)*γ j,mul_pos (by positivity) (hγ j),?_⟩
  intro ε _ hε X _ μ u hu hi hn hnear
  let G (x : X) := ∏ j, (u j x)^γ j
  have small (i : ι) : (∫ x, |u i x-G x| ∂μ) ≤ η/2 := by
    have hδ := hε.le.trans (mul_le_mul_of_nonneg_left (hmin i (Finset.mem_univ i))
      (show 0 ≤ η^2/64 by positivity))
    have h := holder_stability_estimate μ γ hγ hs u hu hi hn ε hnear (η/16) i
    apply le_of_mul_le_mul_left (a := 2*(η/16)*γ i) _ (by positivity [hγ i])
    apply h.trans
    nlinarith only [hδ, mul_nonneg (sq_nonneg η) (hγ i).le]
  have hG : Integrable G μ := by
    have hS : Integrable (fun x => ∑ j, γ j * u j x) μ := integrable_finsetSum _ fun j _ => (hi j).const_mul _
    apply hS.mono' (Finset.aemeasurable_fun_prod Finset.univ fun j _ => (hi j).aemeasurable.pow_const (γ j)).aestronglyMeasurable
    filter_upwards with x
    change ‖G x‖ ≤ ∑ j, γ j * u j x
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hu j x) (γ j)) : 0 ≤ G x)]
    exact Real.geom_mean_le_arith_mean_weighted _ γ (fun j => u j x) (fun j _ => (hγ j).le) hs (fun j _ => hu j x)
  intro i
  refine ⟨(small i).trans (by linarith),?_⟩
  intro j
  have hj : Integrable (fun x => |G x-u j x|) μ := (hG.sub (hi j)).abs
  have hk : Integrable (fun x => |u i x-G x|) μ := ((hi i).sub hG).abs
  calc
    _ ≤ ∫ x, |u i x-G x| + |G x-u j x| ∂μ :=
      integral_mono (((hi i).sub (hi j)).abs) (hk.add hj) (fun x => abs_sub_le ..)
    _ = (∫ x, |u i x-G x| ∂μ) + (∫ x, |u j x-G x| ∂μ) := by
      rw [integral_add hk hj]; congr 1; apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => abs_sub_comm ..)
    _ ≤ η := by linarith [small i, small j]

end LpGowers
