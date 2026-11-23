module

public import LpGowers.DiscreteScalar
public import LpGowers.DiscreteProduct

/-! # The sharp functional bound on the one-dimensional binary interval -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal Pointwise ENNReal

namespace LpGowers.Discrete

theorem box_one_two : box 1 2 = {0,1} := by
  ext x
  have he (z : ℤ) : x = (fun _ => z) ↔ x 0 = z := by
    constructor
    · intro h; simp [h]
    · intro h; funext i; have hi : i = 0 := Subsingleton.elim _ _; simpa [hi] using h
  simp only [box, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
  change (∀ i, 0 ≤ x i ∧ x i < 2) ↔ x = (fun _ => 0) ∨ x = (fun _ => 1)
  rw [he, he]
  constructor
  · intro h; have := h 0; omega
  · intro h i; have hi : i = 0 := Subsingleton.elim _ _; rw [hi]; omega

variable {G : Type*} [AddCommGroup G]

private theorem finiteCubeProduct_zero (d : ℕ) (f : G → ℝ≥0) (x : G) :
    finiteCubeProduct d f 0 x = f x ^ (2^d) := by
  induction d with
  | zero => simp [finiteCubeProduct]
  | succ d ih =>
    change finiteCubeProduct d f 0 x * finiteCubeProduct d f 0 (x+0) = _
    rw [add_zero, ih, pow_succ (2:ℕ), mul_two, pow_add]

private theorem finiteCubeProduct_single (d : ℕ) (f : G → ℝ≥0) (x a : G) (i : Fin (d+1)) :
    finiteCubeProduct (d+1) f (fun j => if j=i then a else 0) x = (f x * f (x+a))^(2^d) := by
  induction d with
  | zero =>
    have hi : i=0 := by omega
    simp [hi, finiteCubeProduct]
  | succ d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [finiteCubeProduct, ite_true, Fin.tail, Fin.succ_ne_zero, ite_false]
      change finiteCubeProduct (d+1) f 0 x * finiteCubeProduct (d+1) f 0 (x+a) = _
      rw [finiteCubeProduct_zero, finiteCubeProduct_zero, mul_pow]
    · change finiteCubeProduct (d+1) f (fun j => if j.succ=i.succ then a else 0) x *
        finiteCubeProduct (d+1) f (fun j => if j.succ=i.succ then a else 0) (x+(if 0=i.succ then a else 0)) = _
      simp only [Fin.succ_inj, Ne.symm i.succ_ne_zero, ite_false, add_zero]
      rw [ih i, pow_succ (2:ℕ), mul_two, pow_add]

/-- Exact formula for the powered Gowers functional of an arbitrary nonnegative
function supported on the one-dimensional binary interval, as in §8. -/
theorem weighted_binary_energy (d k : ℕ) (f : Lattice 1 → ℝ≥0)
    (hf : ∀ x, x ∉ box 1 2 → f x=0) :
    weightedEnergy (d+1) (k+1) (box 1 2) f =
      (f 0^(2^(d+1)) + f 1^(2^(d+1)))^(k+1) +
        2*(d+1 : ℕ)*(f 0*f 1)^(2^d*(k+1)) := by
  rw [box_one_two] at hf ⊢
  let B : Finset (Lattice 1) := {0,1}
  have hoff : f (1+1) = 0 := by
    apply hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h|h) <;> have hh := congrFun h (0:Fin 1) <;> norm_num at hh
  have hneg : f (-1) = 0 := by
    apply hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h|h) <;> have hh := congrFun h (0:Fin 1) <;> norm_num at hh
  have hsign (u : Fin (d+1) × Bool) :
      (∑ x ∈ B, finiteCubeProduct (d+1) f (fun j => if j=u.1 then (if u.2 then 1 else -1) else 0) x) =
        (f 0*f 1)^(2^d) := by
    rcases u with ⟨i,b⟩
    simp only [finiteCubeProduct_single, B, Finset.sum_insert (by simp : (0:Lattice 1) ∉ ({1} : Finset _)),
      Finset.sum_singleton]
    cases b <;> simp [hneg, hoff, mul_comm]
  unfold weightedEnergy
  rw [sum_binary_steps]
  · change _ + ∑ u : Fin (d+1) × Bool, (∑ x ∈ B, _)^(k+1) = _
    simp only [hsign, finiteCubeProduct_zero, ← pow_mul]
    simp [mul_assoc, mul_comm]
  intro h hzero
  have hz (x) (hx : x ∈ B) : finiteCubeProduct (d+1) f h x = 0 := by
    by_contra hn
    have he := finiteCubeProduct_fits hf _ h x hn
    have : 0 < baseCount B h := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,he⟩⟩
    exact this.ne' hzero
  rw [Finset.sum_eq_zero (s := B) hz]
  simp



/-- The one-dimensional functional inequality, with the sharp exponent in
Theorem 1.5(a). The ambient group is the integer lattice with counting measure. -/
theorem binary_one_dimensional_bound (d k : ℕ) (f : Lattice 1 → ℝ≥0)
    (hf : ∀ x, x ∉ box 1 2 → f x=0) :
    let t := logTwo ((2:ℝ)^(k+1)+2*(d+1:ℕ))
    let q := (2:ℝ)^(d+1)*(k+1:ℕ)/t
    gowers Measure.count (d+1) (k+1:ℕ) f ≤ lp Measure.count q (liftNN f) := by
  let t := logTwo ((2:ℝ)^(k+1)+2*(d+1:ℕ))
  let P : ℝ := ((k+1:ℕ):ℝ)
  let v : ℝ := 2^(d+1)*P
  let q := v/t
  have ht : 0 < t := by
    apply Real.logb_pos (by norm_num)
    have h1 : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    have h2 : 0 < ((d+1:ℕ):ℝ) := by positivity
    linarith
  have hP : 0 < P := by dsimp [P]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hq : 0 < q := div_pos hv ht
  change gowers Measure.count (d+1) (k+1:ℕ) f ≤ lp Measure.count q (liftNN f)
  apply (bound_iff_weightedEnergy (d+1) k 2 1 hq f hf).mpr
  rw [weighted_binary_energy d k f hf, box_one_two, Finset.sum_insert (by simp), Finset.sum_singleton]
  have hqt : v/q = t := by dsimp [q]; field_simp
  have e1 : q*(t/P) = (2:ℝ)^(d+1) := by dsimp [q,v]; field_simp
  have e2 : q*(t/2) = (2^d*(k+1):ℕ) := by dsimp [q,v,P]; push_cast; rw [pow_succ]; field_simp
  let a : ℝ := f 0
  let b : ℝ := f 1
  have ha : 0 ≤ a := NNReal.zero_le_coe
  have hb : 0 ≤ b := NNReal.zero_le_coe
  have hs := binary_scalar_sharp (d+1) k (by omega) (a^q) (b^q) (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  change ((a^q)^(t/P)+(b^q)^(t/P))^(k+1)+2*(d+1:ℕ)*(a^q*b^q)^(t/2) ≤ (a^q+b^q)^t at hs
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb, e1, ← Real.mul_rpow ha hb,
    ← Real.rpow_mul (mul_nonneg ha hb), e2, Real.rpow_natCast] at hs
  have eD : (2:ℝ)^(d+1) = ((2^(d+1):ℕ):ℝ) := by push_cast; rfl
  rw [eD, Real.rpow_natCast, Real.rpow_natCast] at hs
  change _ ≤ (f 0 ^ q + f 1 ^ q)^(v/q)
  rw [hqt]
  exact_mod_cast hs



/-- Both sharp exponents in Theorem 1.5(a) follow as soon as the
one-dimensional functional inequality tensorizes. The triangle inequality
and the full converse of Proposition 8.1 are unnecessary in this implication. -/
theorem binaryClaim_of_one_dimensional_extension
    (hext : ∀ (d k : ℕ) (q : ℝ), 0<q →
      (∀ f : Lattice 1 → ℝ≥0, (∀ x, x ∉ box 1 2 → f x=0) →
        gowers Measure.count d (k+1:ℕ) f ≤ lp Measure.count q (liftNN f)) →
      q ∈ functionExponents d (k+1) 2) : BinaryClaim := by
  intro D K hd hp
  obtain ⟨d,rfl⟩ : ∃ u, D = u+1 := ⟨D-1, by omega⟩
  obtain ⟨k,rfl⟩ : ∃ u, K = u+1 := ⟨K-1, by omega⟩
  let t := logTwo ((2:ℝ)^(k+1)+2*(d+1:ℕ))
  let v : ℝ := 2^(d+1)*(k+1:ℕ)
  have hv : 0 < v := by dsimp [v]; positivity
  have ht : 0 < t := by
    apply Real.logb_pos (by norm_num)
    have h1 : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    have h2 : 0 < ((d+1:ℕ):ℝ) := by positivity
    linarith
  have hq := hext (d+1) k (v/t) (div_pos hv ht) (fun f hf => binary_one_dimensional_bound d k f hf)
  have hset := setExponent_of_functionExponent (d+1) k 2 hq
  change v/(v/t) ∈ setExponents (d+1) (k+1) 2 at hset
  have he : v/(v/t) = t := by field_simp
  rw [he] at hset
  have hT := le_antisymm ((criticalT_isLeast (d+1) k 2 le_rfl).2 hset) (binary_criticalT_lower (d+1) k)
  refine ⟨hT, le_antisymm ?_ ((criticalQ_isGreatest (d+1) k 2 le_rfl).2 hq)⟩
  apply (le_div_iff₀ ht).mpr
  rw [← hT]
  exact criticalQ_mul_criticalT_le (d+1) k 2 le_rfl

end LpGowers.Discrete
