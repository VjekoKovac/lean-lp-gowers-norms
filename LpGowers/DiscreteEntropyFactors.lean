module

public import LpGowers.DiscreteEntropyComparison
public import LpGowers.BinomialEntropy
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Geometric factors in the large-degree upper bound

For the diffuse case, weighted arithmetic–geometric mean bounds each factor
by the base-two exponential of the negative entropy. For inputs concentrated
at one point, two distinct vertices supply a quadratic factor. -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
open Real
namespace LpGowers.Discrete

/-- The geometric mean of the weights over cube vertices, raised to t. -/
def subsetMonomial {Z : Type*} (l : ℕ) (F : Finset (Fin l) → Z) (g : Z → ℝ≥0) (t : ℝ) : ℝ≥0 :=
  ∏ s, g (F s) ^ (t/(2:ℝ)^l)

/-- Weighted AM–GM, expressed in terms of the exact Shannon entropy in bits
of the uniform pushforward on the subsets. -/
theorem subsetMonomial_entropy {Z : Type*} [DecidableEq Z] (l : ℕ) (F : Finset (Fin l) → Z)
    (g : Z → ℝ≥0) (hmas : ∑ j ∈ Finset.univ.image F, g j ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (subsetMonomial l F g t : ℝ) ≤ 2^(-subsetEntropy l F * t) := by
  classical
  let S := Finset.univ.image F
  let C (j : Z) := (Finset.univ.filter fun s => F s=j).card
  let a (j : Z) : ℝ := C j/(2:ℝ)^l
  have ha (j : Z) (hj : j∈S) : 0 < a j := by
    apply div_pos _ (by positivity)
    apply Nat.cast_pos.mpr
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hj
    exact Finset.card_pos.mpr ⟨s,by simpa using hs⟩
  have hsum : ∑ j ∈ S, a j = 1 := by
    have h := Finset.card_eq_sum_card_image F (Finset.univ : Finset (Finset (Fin l)))
    rw [← div_self (by positivity : (2:ℝ)^l ≠ 0)]
    dsimp [a]
    rw [← Finset.sum_div]
    congr 1
    dsimp [C,S]
    exact_mod_cast (by simpa using h.symm)
  have ham := Real.geom_mean_le_arith_mean_weighted S a (fun j => (g j : ℝ)/a j)
    (fun j hj => (ha j hj).le) hsum (fun j hj => div_nonneg (by positivity) (ha j hj).le)
  have hS : ∑ j ∈ S, a j*((g j : ℝ)/a j) ≤ 1 := by
    calc
      _ = ∑ j ∈ S, (g j : ℝ) := Finset.sum_congr rfl fun j hj => by field_simp [(ha j hj).ne']
      _ ≤ 1 := by exact_mod_cast hmas
  have hp : (∏ j ∈ S, a j ^ a j) > 0 := Finset.prod_pos fun j hj => Real.rpow_pos_of_pos (ha j hj) _
  have hgeom : ∏ j ∈ S, (g j:ℝ)^a j ≤ ∏ j ∈ S, a j ^ a j := by
    apply (div_le_one hp).mp
    rw [← Finset.prod_div_distrib]
    apply le_trans _ (ham.trans hS)
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro j hj
    rw [Real.div_rpow (by positivity) (ha j hj).le]
  have hnat : ∏ j ∈ S, a j ^ a j = 2^(-subsetEntropy l F) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    unfold subsetEntropy
    change _ = exp (log 2 * -((∑ j ∈ S, Real.negMulLog (a j))/log 2))
    rw [show log 2 * -((∑ j ∈ S, Real.negMulLog (a j))/log 2) =
      ∑ j ∈ S, log (a j)*a j by
      field_simp
      simp [Real.negMulLog,mul_comm]]
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j hj
    exact Real.rpow_def_of_pos (ha j hj) _
  have he : (subsetMonomial l F g t : ℝ) = (∏ j ∈ S, (g j:ℝ)^a j)^t := by
    rw [← Real.finsetProd_rpow S _ (fun _ _ => Real.rpow_nonneg (by positivity) _) t]
    simp only [subsetMonomial, NNReal.coe_prod, NNReal.coe_rpow]
    rw [← Finset.prod_fiberwise_of_maps_to (t := S) (g := F) (fun s _ => Finset.mem_image_of_mem F (Finset.mem_univ s))]
    apply Finset.prod_congr rfl
    intro j hj
    calc
      _ = ∏ _ ∈ Finset.univ.filter (fun s => F s=j), (g j:ℝ)^(t/(2:ℝ)^l) :=
        Finset.prod_congr rfl fun s hs => by rw [(Finset.mem_filter.mp hs).2]
      _ = _ := by
        rw [Finset.prod_const, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_mul (by positivity)]
        congr 1
        dsimp [a,C]
        ring
  rw [he]
  exact (Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _) hgeom ht).trans_eq
    (by rw [hnat, ← Real.rpow_mul (by positivity)])

/-- Two distinct vertices, one of them small, suffice for the concentrated
case. All remaining weights are bounded by one. -/
theorem subsetMonomial_concentrated {Z : Type*} (l : ℕ) (F : Finset (Fin l) → Z) (g : Z → ℝ≥0)
    (s u : Finset (Fin l)) (hsu : s≠u) (hg : ∀ v, g (F v) ≤ 1) (t : ℝ) (θ : ℝ≥0)
    (hθ : g (F u) ≤ θ) (ht : 1 ≤ t/2^l) :
    subsetMonomial l F g t ≤ g (F s)*g (F u)*θ^(t/2^l-1) := by
  classical
  let e := t/(2:ℝ)^l
  have ht0 : 0 ≤ e := (by norm_num : (0:ℝ)≤1).trans ht
  have hsmall : ∀ v, g (F v)^e ≤ 1 := fun v => by
    simpa using NNReal.rpow_le_rpow (hg v) ht0
  have hprod := Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ ({s,u} : Finset (Finset (Fin l))))
    (f := fun v => g (F v)^e) (fun v _ _ => hsmall v)
  rw [Finset.prod_insert (by simpa using hsu), Finset.prod_singleton] at hprod
  apply hprod.trans
  calc
    _ ≤ g (F s)^ (1:ℝ) * (g (F u)^ (1:ℝ)*g (F u)^(e-1)) := by
      rw [← NNReal.rpow_add_of_nonneg _ (by norm_num) (sub_nonneg.mpr ht), add_sub_cancel]
      rw [NNReal.rpow_one]
      exact mul_le_mul_of_nonneg_right (NNReal.rpow_le_self_of_le_one (hg s) ht) zero_le
    _ ≤ _ := by simp only [NNReal.rpow_one]; rw [← mul_assoc]; gcongr

end LpGowers.Discrete
