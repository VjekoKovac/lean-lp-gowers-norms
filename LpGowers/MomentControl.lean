module

public import LpGowers.MomentDeficit
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A threshold set from three moments

Scalar estimates for the threshold `{x | 1/2 < F x}` in Lemma 6.2 of
Kovač and Rogers. The square-root deficit controls the tails. On a compact
interval strictly inside the positive half-line, the deficit vanishes only
at one. -/

@[expose] public section
noncomputable section
namespace LpGowers

private theorem compact_deficit {s : Set ℝ} (hs : IsCompact s) (D E : ℝ → ℝ)
    (hD : Continuous D) (hE : Continuous E) (hn : ∀ x, 0 ≤ D x)
    (hz : ∀ x ∈ s, D x = 0 → E x = 0) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, E x ≤ η + C * D x := by
  let bad := s ∩ {x : ℝ | η ≤ E x}
  have hb : IsCompact bad := hs.inter_right (isClosed_le continuous_const hE)
  by_cases hne : bad.Nonempty
  · obtain ⟨u, hu, hmin⟩ := hb.exists_isMinOn hne hD.continuousOn
    obtain ⟨v, hv, hmax⟩ := hb.exists_isMaxOn hne hE.continuousOn
    have hu' : 0 < D u := lt_of_le_of_ne (hn u) (by
      intro h
      have h0 := hz u hu.1 h.symm
      have hηu : η ≤ E u := hu.2
      linarith)
    have hv' : 0 ≤ E v := hη.le.trans hv.2
    refine ⟨E v / D u, div_nonneg hv' hu'.le, ?_⟩
    intro x hx
    by_cases hx' : η ≤ E x
    · have hmem : x ∈ bad := ⟨hx,hx'⟩
      have h1 : D u ≤ D x := hmin hmem
      have h2 : E x ≤ E v := hmax hmem
      have h3 := mul_le_mul_of_nonneg_left h1 (div_nonneg hv' hu'.le)
      rw [div_mul_cancel₀ _ hu'.ne'] at h3
      linarith
    · exact (le_of_not_ge hx').trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hv' hu'.le) (hn x)))
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    simpa using (le_of_not_ge fun h => hne ⟨x,hx,h⟩ : E x ≤ η)

private theorem sqrt_powers_factor {x a c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hac : a ≤ c) :
    Real.sqrt (x ^ c) = Real.sqrt (x ^ a) * x ^ ((c-a)/2) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, ← Real.rpow_mul hx,
    ← Real.rpow_add_of_nonneg hx (by positivity) (by linarith)]
  congr 1
  ring

/-- Both errors associated with the cutoff at 1/2 are uniformly small relative
to the endpoint densities when the square-root deficit is small. -/
theorem moment_error_domination {a c t η : ℝ} (ha : 0 < a) (hac : a < c)
    (hat : a ≤ t) (htc : t ≤ c) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      |x - (if 1/2 < x then 1 else 0)| ^ t + |x^c - (if 1/2 < x then 1 else 0)| ≤
        η * (x^a+x^c) + C * (Real.sqrt (x^a) - Real.sqrt (x^c))^2 := by
  let r := (c-a)/2
  let k := (1/2 : ℝ)^r
  let D (x : ℝ) := (Real.sqrt (x^a) - Real.sqrt (x^c))^2
  let E (x : ℝ) := |x-1|^t + |x^c-1|
  have hr : 0 < r := by dsimp [r]; linarith
  have ht : 0 < t := ha.trans_le hat
  have hc : 0 < c := ha.trans hac
  have hk : k < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hr
  have hk' : 0 ≤ k := Real.rpow_nonneg (by norm_num) _
  have hlo : 0 < (1-k)^2 := sq_pos_of_pos (sub_pos.mpr hk)
  have hD : Continuous D := by
    exact ((Real.continuous_rpow_const ha.le).sqrt.sub (Real.continuous_rpow_const hc.le).sqrt).pow 2
  have hE : Continuous E := by
    exact ((Real.continuous_rpow_const ht.le).comp (continuous_id.sub continuous_const).abs).add
      ((Real.continuous_rpow_const hc.le).sub continuous_const).abs
  have hnon (x : ℝ) : 0 ≤ D x := sq_nonneg _
  have hz (x : ℝ) (hx : x ∈ Set.Icc (1/2 : ℝ) 2) (h0 : D x = 0) : E x = 0 := by
    have hx' : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have h : Real.sqrt (x^a) = Real.sqrt (x^c) := by
      change (Real.sqrt (x^a) - Real.sqrt (x^c))^2 = 0 at h0
      nlinarith
    have h' : x^a = x^c := by
      have := congrArg (fun u : ℝ => u^2) h
      simpa [Real.sq_sqrt (Real.rpow_nonneg hx'.le _)] using this
    rcases lt_trichotomy x 1 with lo | eq | hi
    · exact ((Real.rpow_lt_rpow_of_exponent_gt hx' lo hac).ne h'.symm).elim
    · simp [E,eq,Real.zero_rpow ht.ne']
    · exact ((Real.rpow_lt_rpow_of_exponent_lt hi hac).ne h').elim
  obtain ⟨M,hM,hmid⟩ := compact_deficit isCompact_Icc D E hD hE hnon hz
    (mul_pos hη (Real.rpow_pos_of_pos (by norm_num : 0 < (1/2:ℝ)) a))
  let C := max M (2/(1-k)^2)
  have hC : 0 ≤ C := hM.trans (le_max_left ..)
  refine ⟨C,hC,?_⟩
  intro x hx
  have hxa := Real.rpow_nonneg hx a
  have hxc := Real.rpow_nonneg hx c
  have hsum := mul_nonneg hη.le (add_nonneg hxa hxc)
  have hroot := sqrt_powers_factor hx ha.le hac.le
  have tail (y : ℝ) (h : (1-k)^2*y ≤ D x) : 2*y ≤ η*(x^a+x^c)+C*D x := by
    have hj := mul_le_mul_of_nonneg_left h (show 0 ≤ 2/(1-k)^2 by positivity)
    rw [← mul_assoc, div_mul_cancel₀ _ hlo.ne'] at hj
    exact hj.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (hnon x)).trans
      (le_add_of_nonneg_left hsum))
  by_cases tiny : x ≤ 1/2
  · rw [ite_eq_right (not_lt.mpr tiny), sub_zero, sub_zero, abs_of_nonneg hx, abs_of_nonneg hxc]
    have hu : x ≤ 1 := by linarith
    have hv : Real.sqrt (x ^ c) ≤ k * Real.sqrt (x ^ a) := by
      rw [hroot, mul_comm k]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx tiny hr.le) (Real.sqrt_nonneg _)
    have hw : 0 ≤ (1-k)*Real.sqrt (x^a) := mul_nonneg (sub_nonneg.mpr hk.le) (Real.sqrt_nonneg _)
    have hs : ((1-k)*Real.sqrt (x^a))^2 ≤ D x := by
      apply pow_le_pow_left₀ hw _ 2
      linarith
    rw [mul_pow, Real.sq_sqrt hxa] at hs
    exact (add_le_add (Real.rpow_le_rpow_of_exponent_ge' hx hu ha.le hat)
      (Real.rpow_le_rpow_of_exponent_ge' hx hu ha.le hac.le)).trans
      ((by linarith : x^a + x^a ≤ 2*x^a).trans (tail _ hs))
  · rw [ite_eq_left (lt_of_not_ge tiny)]
    by_cases huge : 2 ≤ x
    · have hx1 : 1 ≤ x := by linarith
      have hp : 1 ≤ k * x^r := by
        rw [← Real.mul_rpow (by norm_num : 0 ≤ (1/2:ℝ)) hx]
        exact Real.one_le_rpow (by linarith) hr.le
      have hv : Real.sqrt (x^a) ≤ k*Real.sqrt (x^c) := by
        rw [hroot]
        have := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg (x^a))
        simpa only [r, mul_one, mul_left_comm] using this
      have hw : 0 ≤ (1-k)*Real.sqrt (x^c) := mul_nonneg (sub_nonneg.mpr hk.le) (Real.sqrt_nonneg _)
      have hs : ((1-k)*Real.sqrt (x^c))^2 ≤ (Real.sqrt (x^c)-Real.sqrt (x^a))^2 := by
        apply pow_le_pow_left₀ hw _ 2
        linarith
      rw [mul_pow, Real.sq_sqrt hxc, ← neg_sub (Real.sqrt (x^a)), neg_sq] at hs
      rw [abs_of_nonneg (sub_nonneg.mpr hx1), abs_of_nonneg (sub_nonneg.mpr (Real.one_le_rpow hx1 hc.le))]
      have hlt := (Real.rpow_le_rpow (sub_nonneg.mpr hx1) (show x-1 ≤ x by linarith) ht.le).trans
        (Real.rpow_le_rpow_of_exponent_le hx1 htc)
      exact (by linarith : (x-1)^t + (x^c-1) ≤ 2*x^c).trans (tail _ hs)
    · have hx' := hmid x ⟨(lt_of_not_ge tiny).le, (lt_of_not_ge huge).le⟩
      apply hx'.trans
      exact add_le_add (mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow (by norm_num) (lt_of_not_ge tiny).le ha.le).trans (le_add_of_nonneg_right hxc)) hη.le)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnon x))

end LpGowers
