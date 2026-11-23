module

public import LpGowers.PowerTransfer
public import LpGowers.Normalization

/-! # The Eisner–Tao input to Theorem 1.2(b)

The hypothesis below is the nonnegative, unit-critical-moment consequence of
Eisner and Tao, *Large values of the Gowers–Host–Kra seminorms*, Theorem 1.10
as cited in Kovač–Rogers (Theorem 1.4 in arXiv:1012.3509).
The polynomial phase drops out on taking absolute values. A project proof of
that inverse theorem would discharge the single external hypothesis of
`lebesgueStability_of_ordinaryInverse`. -/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace LpGowers

/-- Uniform inverse theorem for the ordinary Gowers inequality at `p=1`.
The amplitude is specified by the Haar mass of the
compact open subgroup. Only the nonnegative specialization is required. -/
def OrdinaryGowersInverse.{u} : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ η : ℝ, 0 < η → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0), AEMeasurable f μ →
      (∫⁻ x, (f x : ℝ≥0∞) ^ criticalExponent d 1 ∂μ) = 1 →
      ENNReal.ofReal (1-α) ≤ ordinaryGowers μ d f →
      ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
        lpDist μ (criticalExponent d 1) f (cosetProfile μ (criticalExponent d 1) 1 H x₀) ≤
          ENNReal.ofReal η

private def nearWeight (d : ℕ) (p : ℝ) : ℝ :=
  if 1 ≤ p then 1/p else 1-(d : ℝ)*(1-p)/(((2:ℝ)^d-d-1)*p)

private theorem nearWeight_pos {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : lowerEndpoint d < p) :
    0 < nearWeight d p := by
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hK : 1 < (2:ℝ)^d := one_lt_pow₀ (by norm_num) (by omega)
  have hp' : 0 < p := lt_trans (div_pos hD (sub_pos.mpr hK)) hp
  by_cases h : 1 ≤ p
  · simpa [nearWeight,h] using one_div_pos.mpr hp'
  · have hDp : (d:ℝ) < p * (2^d-1) := (div_lt_iff₀ (sub_pos.mpr hK)).mp hp
    have hKD : 0 < (2:ℝ)^d-d-1 := by
      linarith only [hDp,mul_lt_mul_of_pos_right (lt_of_not_ge h) (sub_pos.mpr hK)]
    rw [nearWeight, ite_eq_right h, sub_pos, div_lt_one (mul_pos hKD hp')]
    linarith only [hDp]

/-- The normalized near-extremiser implication, with all parameters uniform
in the group, its Haar normalization, and the function. -/
theorem unitStability_of_ordinaryInverse.{u} (hET : OrdinaryGowersInverse.{u}) :
    NormalizedLebesgueStability.{u} := by
  intro d hd p hp η hη
  let q := criticalExponent d p
  let r := criticalExponent d 1
  let t := ordinaryInputPower d p
  let γ := 1/t
  let w := nearWeight d p
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hK : 1 < (2:ℝ)^d := one_lt_pow₀ (by norm_num) (by omega)
  have hp' : 0 < p := lt_trans (div_pos hD (sub_pos.mpr hK)) hp
  have hr : 0 < r := by dsimp [r, criticalExponent]; positivity
  have ht : 0 < t := by dsimp [t, ordinaryInputPower]; positivity
  have hγ : 0 < γ := one_div_pos.mpr ht
  have hw : 0 < w := nearWeight_pos hd hp
  have hrq : r/γ = q := by
    dsimp [r,γ,t,q,ordinaryInputPower,criticalExponent]
    field_simp
  obtain ⟨τ,hτ,htransport⟩ := power_transfer_tolerance.{u} hr hγ hη
  obtain ⟨α,hα,hα1,hcoset⟩ := hET d hd τ hτ
  let δ := 1-(1-α)^w
  have hδ : 0 < δ :=
    sub_pos.mpr (Real.rpow_lt_one (sub_nonneg.mpr hα1.le) (by linarith) hw)
  refine ⟨δ,hδ,?_⟩
  intro ε _ hε G _ _ _ _ _ _ _ _ μ _ f hf hmass hnear
  let U := fun x => f x ^ t
  have hU : AEMeasurable U μ := hf.pow_const _
  have hUmass : (∫⁻ x, (U x : ℝ≥0∞)^r ∂μ) = 1 :=
    (transformed_critical_moment μ d hp' f).trans hmass
  have hUbound : gowers μ d p f ≤ ordinaryGowers μ d U ^ w := by
    by_cases h : 1 ≤ p
    · simpa [w,nearWeight,h,U,t] using stability_reduction_ge_one μ d h hf hmass
    · simpa [w,nearWeight,h,U,t] using
        (stability_reduction_lt_one μ d hd hp (lt_of_not_ge h) hf hmass).2
  have hUlower : ENNReal.ofReal (1-α) ≤ ordinaryGowers μ d U := by
    apply (ENNReal.rpow_le_rpow_iff hw).mp
    rw [ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hα1.le) hw.le]
    exact (ENNReal.ofReal_le_ofReal (by dsimp [δ] at hε; linarith)).trans (hnear.trans hUbound)
  obtain ⟨H,x₀,hc,ho,herr⟩ := hcoset G μ U hU hUmass hUlower
  let V := cosetProfile μ r 1 H x₀
  have hV : AEMeasurable V μ := by
    apply Measurable.aemeasurable
    classical
    exact Measurable.ite ((measurable_id.sub_const x₀) ho.measurableSet) measurable_const measurable_const
  have hVm := cosetProfile_unit_moment μ r hr H x₀ hc ho
  have hpow := htransport G μ U V hU hV hUmass hVm herr
  have hID : (fun x => U x ^ γ) = f := by
    funext x
    simp [U,γ,← NNReal.rpow_mul,ht.ne']
  change lpDist μ (r/γ) (fun x => U x ^ γ) (fun x => cosetProfile μ r 1 H x₀ x ^ γ) ≤ _ at hpow
  rw [hID, cosetProfile_unit_rpow μ r γ hr hγ H x₀ hc ho, hrq] at hpow
  exact ⟨H,x₀,hc,ho,hpow⟩

/-- The complete stability clause follows from the ordinary Gowers inverse theorem. -/
theorem lebesgueStability_of_ordinaryInverse.{u} (hET : OrdinaryGowersInverse.{u}) :
    LebesgueStability.{u} :=
  lebesgueStability_of_unit (unitStability_of_ordinaryInverse hET)

/-- The ordinary inverse statement is itself the `p=1` specialization of
the claimed stability clause, restricted to unit critical moment. -/
theorem ordinaryInverse_of_lebesgueStability.{u} (hS : LebesgueStability.{u}) :
    OrdinaryGowersInverse.{u} := by
  intro d hd η hη
  have hB : d + 1 < 2 ^ d := by
    induction d, hd using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  have hBR : (d:ℝ)+1 < (2:ℝ)^d := by exact_mod_cast hB
  have hden : 0 < (2:ℝ)^d-1 := by linarith only [hBR,Nat.cast_nonneg (α := ℝ) d]
  have he : lowerEndpoint d < 1 := (div_lt_one hden).mpr (by linarith only [hBR])
  obtain ⟨δ,hδ,hnear⟩ := hS d hd 1 he η hη
  let α := min (δ/2) (1/2)
  have hα : 0 < α := lt_min (half_pos hδ) (by norm_num)
  have hαl : α < δ := lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)
  have hαr : α < 1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  refine ⟨α,hα,hαr,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf hmass hU
  have hr : 0 < criticalExponent d 1 := by unfold criticalExponent; positivity
  have hNZ : ¬ (f =ᵐ[μ] fun _ => 0) := by
    intro hz
    have h := (lintegral_eq_zero_iff' (hf.coe_nnreal_ennreal.pow_const (criticalExponent d 1))).mpr (by
      filter_upwards [hz] with x hx
      simp [hx,ENNReal.zero_rpow_of_pos hr])
    rw [hmass] at h
    exact one_ne_zero h
  have hNorm : lp μ (criticalExponent d 1) (liftNN f) = 1 := by simp [lp,liftNN,hmass]
  have hU' : ENNReal.ofReal (1-α) * lp μ (criticalExponent d 1) (liftNN f) ≤ gowers μ d 1 f := by
    simpa [hNorm,ordinaryGowers] using hU
  obtain ⟨H,x₀,hc,ho,herr⟩ := hnear α hα hαl G μ f hf hNZ (by simp [hNorm]) hU'
  exact ⟨H,x₀,hc,ho,by simpa [hNorm] using herr⟩

/-- With the Lebesgue bound proved unconditionally, the full second theorem
is equivalent to this particular ordinary inverse theorem of Eisner and Tao. -/
theorem lebesgueEstimate_iff_ordinaryInverse.{u} :
    LebesgueEstimate.{u} ↔ OrdinaryGowersInverse.{u} :=
  ⟨fun h => ordinaryInverse_of_lebesgueStability h.2,
    fun h => ⟨lebesgueBound,lebesgueStability_of_ordinaryInverse h⟩⟩

end LpGowers
