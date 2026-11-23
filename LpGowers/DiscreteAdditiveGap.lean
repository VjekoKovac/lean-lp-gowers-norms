module

public import LpGowers.DiscreteConcentration
public import LpGowers.DiscreteFiniteNorm
public import LpGowers.DiscreteGapParameters
public import LpGowers.DiscreteTensorization
public import LpGowers.DiscretePeak

/-! # An absolute upper correction for the large-side exponent

Use the lattice specialization of the inverse estimate in Theorem 1.2.
Away from point masses the uniform gap pays for the support-size norm loss.
Near a point mass the absence of the linear term pays for the same loss.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers.Discrete

private theorem split_mass {m : ℕ} (f : Lattice m → ℝ≥0) (x₀ : Lattice m) {q : ℝ}
    (hq : 0<q) :
    (f x₀ : ℝ≥0∞)^q + (lp Measure.count q (liftNN (({x₀}ᶜ : Set (Lattice m)).indicator f)))^q =
       ∫⁻ x, (f x : ℝ≥0∞)^q ∂Measure.count := by
  classical
  let g := fun x => (f x : ℝ≥0∞)^q
  rw [lp, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  have he (x : Lattice m) : (liftNN (({x₀}ᶜ : Set (Lattice m)).indicator f) x)^q =
       ({x₀}ᶜ : Set (Lattice m)).indicator g x := by
    by_cases h : x=x₀ <;> simp [g,liftNN,h,ENNReal.zero_rpow_of_pos hq]
  simp_rw [he]
  rw [lintegral_indicator (measurableSet_singleton _).compl]
  have hs := lintegral_add_compl g (measurableSet_singleton x₀) (μ := Measure.count)
  simpa only [lintegral_singleton, Measure.count_singleton, mul_one, g] using hs

private theorem gap_unit {n : ℕ} {δ q : ℝ} (hd : 0<δ) (hd' : δ<1)
    (hrq : 4/3 ≤ q) (hq' : q ≤ 3/2)
    (hD : (n:ℝ)^(1/(4/3:ℝ)-1/q) ≤ 2) (hdD : (1-δ)*(n:ℝ)^(1/(4/3:ℝ)-1/q) ≤ 1)
    (f : Lattice 1 → ℝ≥0) (hf : ∀ x ∉ box 1 n, f x=0)
    (h1 : (∫⁻ x, (f x:ℝ≥0∞)^q ∂Measure.count) = 1)
    (hnear : let N := lp Measure.count (4/3) (liftNN f)
      ENNReal.ofReal (1-δ)*N ≤ gowers Measure.count 2 1 f →
      ∃ x₀ : Lattice 1, lp Measure.count (4/3) (liftNN (({x₀}ᶜ : Set (Lattice 1)).indicator f))
        ≤ ENNReal.ofReal (1/20000)*N)
    (hpoint : ∀ x₀ : Lattice 1, let a : ℝ≥0∞ := f x₀
      let T := lp Measure.count (4/3) (liftNN (({x₀}ᶜ : Set (Lattice 1)).indicator f))
      (gowers Measure.count 2 1 f)^4 ≤ a^4 + 11*T^2*(max a T)^2) :
    gowers Measure.count 2 1 f ≤ 1 := by
  classical
  let N := lp Measure.count (4/3) (liftNN f)
  let U := gowers Measure.count 2 1 f
  let C := (n:ℝ)^(1/(4/3:ℝ)-1/q)
  have hq : 0<q := by linarith
  have hr : 0<(4/3:ℝ) := by norm_num
  have hpow : 0 ≤ 1/(4/3:ℝ)-1/q := sub_nonneg.mpr (one_div_le_one_div_of_le hr hrq)
  have hc0 : 0≤C := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hc : (n:ℝ≥0∞)^(1/(4/3:ℝ)-1/q) = ENNReal.ofReal C := by
    dsimp [C]
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n) hpow
  have hnorm : lp Measure.count q (liftNN f) = 1 := by simp [lp,liftNN,h1]
  have hN := lp_le_card_mul_lp hf hr hrq
  rw [card_box, pow_one, hc, hnorm, mul_one] at hN
  change N ≤ ENNReal.ofReal C at hN
  have h2 : N ≤ 2 := hN.trans ((ENNReal.ofReal_le_ofReal hD).trans_eq (by norm_num))
  have hU : U ≤ N := by
    have h := lebesgue_bound_degree_two Measure.count (f:=f) (by norm_num : (2/3:ℝ)≤1)
      (measurable_of_countable _).aemeasurable
    simpa only [show criticalExponent 2 1 = 4/3 by norm_num [criticalExponent]] using h
  by_cases hn : ENNReal.ofReal (1-δ)*N ≤ U
  · obtain ⟨x₀,hx⟩ := hnear hn
    let a : ℝ≥0∞ := f x₀
    let w := ({x₀}ᶜ : Set (Lattice 1)).indicator f
    let T := lp Measure.count (4/3) (liftNN w)
    let S := lp Measure.count q (liftNN w)
    have hw : ∀ x ∉ box 1 n, w x=0 := by intro x hx; by_cases h : x=x₀ <;> simp [w,h,hf x hx]
    have hSfin : S ≠ ⊤ := by rw [show S=lp Measure.count q (liftNN w) from rfl, lp_count_finite _ _ hw hq]; exact ENNReal.coe_ne_top
    have hT : T ≤ ENNReal.ofReal (1/10000) := calc
      _ ≤ ENNReal.ofReal (1/20000)*N := hx
      _ ≤ ENNReal.ofReal (1/20000)*2 := mul_le_mul_right h2 _
      _ = _ := by rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/20000)]; norm_num
    have hTfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT
    have hT' : T ≤ 2*S := by
      have h := lp_le_card_mul_lp hw hr hrq
      rw [card_box, pow_one, hc] at h
      exact h.trans (mul_le_mul_left ((ENNReal.ofReal_le_ofReal hD).trans_eq (by norm_num)) _)
    have hUfin : U ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (hU.trans h2)
    have ha : a ≠ ⊤ := ENNReal.coe_ne_top
    have hS : a^q+S^q=1 := (split_mass f x₀ hq).trans h1
    have hReal := congrArg ENNReal.toReal hS
    rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_nonneg hq.le ha)
      (ENNReal.rpow_ne_top_of_nonneg hq.le hSfin),← ENNReal.toReal_rpow,← ENNReal.toReal_rpow,ENNReal.toReal_one] at hReal
    have hMax : max a T ≠ ⊤ := max_ne_top ha hTfin
    have hE : U^4 ≤ a^4 + 11*T^2*(max a T)^2 := hpoint x₀
    have hEr := ENNReal.toReal_mono (show a^4 + 11*T^2*(max a T)^2 ≠ ⊤ by finiteness) hE
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hEr
    simp only [ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_max ha hTfin] at hEr
    refine (ENNReal.toReal_le_toReal hUfin ENNReal.one_ne_top).mp ?_
    rw [ENNReal.toReal_one]
    apply additive_gap_absorb hq hq' ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hReal _ _ hEr
    · simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by finiteness) hT'
  · apply (le_of_not_ge hn).trans
    calc
      _ ≤ ENNReal.ofReal (1-δ)*ENNReal.ofReal C := mul_le_mul_right hN _
      _ = ENNReal.ofReal ((1-δ)*C) := (ENNReal.ofReal_mul (sub_nonneg.mpr hd'.le)).symm
      _ ≤ 1 := (ENNReal.ofReal_le_ofReal hdD).trans_eq (by norm_num)

/-- An absolute gain of order the reciprocal binary logarithm for ordinary
additive energy in every integer cube, proved via inverse Young on the lattice. -/
theorem additive_energy_upper_gap : ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, 2≤n →
    criticalT 2 1 n ≤ 3 - c/logTwo n := by
  obtain ⟨δ,hd,hd',stab⟩ := near_additive_energy_point (1/20000) (by norm_num)
  obtain ⟨c,hc,par⟩ := additive_gap_parameters hd hd'
  refine ⟨c,hc,?_⟩
  intro n hn
  let t := 3-c/logTwo n
  let q := 4/t
  obtain ⟨hrq,hq',hD,hdD⟩ := par n hn
  have hq : 0<q := (by norm_num : (0:ℝ)<4/3).trans_le hrq
  have hor : q ∈ functionExponents 2 1 n := by
    apply functionExponent_of_one_dimensional 2 0 n hq
    intro f hf
    norm_num only [Nat.zero_add,Nat.cast_one]
    change gowers Measure.count 2 1 f ≤ lp Measure.count q (liftNN f)
    by_cases hz : f =ᵐ[Measure.count] fun _ => 0
    · rw [(gowers_eq_zero_iff Measure.count 2 (by norm_num : (0:ℝ)<1)
        (measurable_of_countable f).aemeasurable).mpr hz]
      exact zero_le
    have hfin : lp Measure.count q (liftNN f) < ⊤ := by
      rw [lp_count_finite _ _ hf hq]; exact ENNReal.coe_lt_top
    obtain ⟨a,F,ha,he,hFM,h1,hfscale⟩ := exists_unit_amplitude Measure.count q hq f
      (measurable_of_countable f).aemeasurable hz hfin
    have hFs : ∀ x ∉ box 1 n, F x=0 := by
      intro x hx
      exact (mul_eq_zero.mp ((congrFun hfscale x).trans (hf x hx))).resolve_left ha.ne'
    have hFn : ¬F =ᵐ[Measure.count] fun _ => 0 := by
      intro hh
      apply hz
      filter_upwards [hh] with x hx
      exact (congrFun hfscale x).symm.trans (by simp [hx])
    have hFN : lp Measure.count (4/3) (liftNN F) < ⊤ := by
      rw [lp_count_finite _ _ hFs (by norm_num : (0:ℝ)<4/3)]; exact ENNReal.coe_lt_top
    have hu := gap_unit hd hd' hrq hq' hD hdD F hFs h1 (stab 1 F hFn hFN)
      (additive_energy_point_tail 1 F)
    calc
      _ = (a:ℝ≥0∞)*gowers Measure.count 2 1 F := hfscale ▸ gowers_smul_input Measure.count a 2 F zero_lt_one
      _ ≤ (a:ℝ≥0∞)*1 := mul_le_mul_right hu _
      _ = _ := (mul_one _).trans he
  have ht := (criticalT_isLeast 2 0 n hn).2 (setExponent_of_functionExponent 2 0 n hor)
  convert ht using 1
  change t = 2^2*((0+1:ℕ):ℝ)/q
  dsimp [q]
  norm_num

/-- The upper half of (1.13), uniformly for every integer side length at
least two, degree at least two and positive integer outer exponent. -/
theorem criticalT_upper_gap : ∃ c : ℝ, 0<c ∧ ∀ d p n : ℕ, 2≤d → 1≤p → 2≤n →
    criticalT d p n ≤ (d:ℝ)+p-c/logTwo n := by
  obtain ⟨c,hc,H⟩ := additive_energy_upper_gap
  refine ⟨c,hc,?_⟩
  intro d p n hd hp hn
  obtain ⟨j,rfl⟩ : ∃ j, d=j+2 := ⟨d-2,by omega⟩
  obtain ⟨k,rfl⟩ : ∃ k, p=k+1 := ⟨p-1,by omega⟩
  have h := criticalT_le_additive_energy j k n
  push_cast
  linarith only [h,H n hn]

end LpGowers.Discrete
