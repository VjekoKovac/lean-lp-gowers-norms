module

public import LpGowers.Euclidean
public import LpGowers.LebesgueTheorem
import LpGowers.Nonvanishing
import Mathlib.Topology.Connected.Clopen

/-! # A dimension-uniform Euclidean gap

The compact open cosets in Theorem 1.2 cannot exist in a positive-dimensional
real vector space. Consequently its conclusion gives an unconditional strict
upper bound for the Euclidean inequality, including exponents below one.
The sharp factor and its Gaussian inverse statement are treated separately.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

/-- A positive-dimensional Euclidean space has no compact open additive subgroup. -/
theorem euclidean_no_compact_open (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ H : AddSubgroup (Rn n), IsCompact (H : Set (Rn n)) ∧ IsOpen (H : Set (Rn n)) := by
  rintro ⟨H,hc,ho⟩
  have hu := IsClopen.eq_univ (show IsClopen (H : Set (Rn n)) from ⟨hc.isClosed,ho⟩)
    (show (H : Set (Rn n)).Nonempty from ⟨0,H.zero_mem⟩)
  let i : Fin n := ⟨0,hn⟩
  have image : (fun x : Rn n => x i) '' (H : Set (Rn n)) = (Set.univ : Set ℝ) := by
    rw [hu,Set.image_univ]
    exact Set.range_eq_univ.mpr (fun x => ⟨fun _ => x,rfl⟩)
  exact (hc.image (continuous_apply i)).ne_univ image

/-- For every interior admissible exponent there is a strict improvement over
one that works for every positive Euclidean dimension. -/
theorem euclidean_strict_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : lowerEndpoint d < p) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ n : ℕ, 1 ≤ n →
      EuclideanBound d n p (ENNReal.ofReal (1-ε)) := by
  obtain ⟨δ,hδ,inv⟩ := lebesgueEstimate.2 d hd p hp 1 (by norm_num)
  let ε := min (δ/2) (1/2)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)
  refine ⟨ε,hε,hε1,?_⟩
  intro n hn f hf
  let μ := euclideanMeasure n
  let : μ.IsAddHaarMeasure := by dsimp [μ,euclideanMeasure]; infer_instance
  let N := lp μ (criticalExponent d p) (liftNN f)
  change gowers μ d p f ≤ ENNReal.ofReal (1-ε)*N
  by_cases hNt : N = ⊤
  · rw [hNt,ENNReal.mul_top (ENNReal.ofReal_pos.mpr (sub_pos.mpr hε1)).ne']
    exact le_top
  by_cases hz : f =ᵐ[μ] 0
  · have hpos : 0 < p := lt_trans (div_pos (by exact_mod_cast (show 0<d by omega))
      (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega : d ≠ 0)))) hp
    rw [(gowers_eq_zero_iff μ d hpos hf).mpr hz]
    exact zero_le
  apply le_of_lt
  by_contra! near
  obtain ⟨H,x₀,hc,ho,_⟩ := inv ε hε hεδ (Rn n) μ f hf hz (lt_top_iff_ne_top.mpr hNt) near
  exact euclidean_no_compact_open n hn ⟨H,hc,ho⟩

end LpGowers
