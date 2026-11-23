module

public import LpGowers.LebesgueTheorem
public import LpGowers.DiscreteFunctional
import Mathlib.GroupTheory.OrderOfElement

/-! # The lattice alternative for near equality in additive energy

The compact open subgroup furnished by Theorem 1.2 on an integer lattice
is finite and torsion-free, so its only element is zero. Thus the first
alternative in the sharpness argument for additive energy is quantitative
concentration outside a single lattice point.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers.Discrete

theorem compact_lattice_subgroup_eq_bot {m : ℕ} {H : AddSubgroup (Lattice m)}
    (hH : IsCompact (H : Set (Lattice m))) : H = ⊥ := by
  let : Finite H := hH.finite_of_discrete.to_subtype
  apply le_antisymm _ bot_le
  intro x hx
  let X : H := ⟨x,hx⟩
  obtain ⟨k,hk,he⟩ := (isOfFinAddOrder_of_finite X).exists_nsmul_eq_zero
  have hx' : k • x = 0 := congrArg H.subtype he
  exact IsOfFinAddOrder.eq_zero' (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k,hk,hx'⟩)

private theorem count_haar (m : ℕ) : (Measure.count : Measure (Lattice m)).IsAddHaarMeasure where
  lt_top_of_isCompact _K hK := Measure.count_apply_lt_top.mpr hK.finite_of_discrete
  open_pos _U _hU hne := Measure.count_ne_zero_iff.mpr hne

/-- The relative `ℓ^{4/3}` norm of a near extremiser outside a single point
can be made arbitrarily small, uniformly in the lattice dimension. -/
theorem near_additive_energy_point (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ (m : ℕ) (f : Lattice m → ℝ≥0),
    ¬(f =ᵐ[Measure.count] fun _ => 0) →
    let N := lp Measure.count (4/3) (liftNN f)
    N < ⊤ → ENNReal.ofReal (1-δ)*N ≤ gowers Measure.count 2 1 f →
    ∃ x₀ : Lattice m,
      lp Measure.count (4/3) (liftNN (({x₀}ᶜ : Set (Lattice m)).indicator f)) ≤ ENNReal.ofReal η * N := by
  have hlow : lowerEndpoint 2 < 1 := by norm_num [lowerEndpoint]
  obtain ⟨d,hd,H⟩ := lebesgueEstimate.{0}.2 2 (by decide) 1 hlow η hη
  let δ := min (d/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hd) (by norm_num)
  refine ⟨δ,hδ, (min_le_right ..).trans_lt (by norm_num),?_⟩
  intro m f hn N hN hg
  let := count_haar m
  have hq : criticalExponent 2 1 = 4/3 := by norm_num [criticalExponent]
  obtain ⟨H,x₀,hc,ho,hL⟩ := H δ hδ ((min_le_left ..).trans_lt (half_lt_self hd))
      (Lattice m) Measure.count f (measurable_of_countable _).aemeasurable hn
      (by simpa only [hq] using hN) (by simpa only [hq] using hg)
  rw [compact_lattice_subgroup_eq_bot hc,hq] at hL
  refine ⟨x₀, le_trans ?_ hL⟩
  unfold lpDist lp
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply lintegral_mono; intro x
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  by_cases hx : x=x₀
  · subst x; simp [liftNN]
  · have hx' : x-x₀ ≠ 0 := sub_ne_zero.mpr hx
    simp [cosetProfile,liftNN,hx,hx',edist_dist,NNReal.dist_eq]

end LpGowers.Discrete
