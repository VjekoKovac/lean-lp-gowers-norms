module

public import LpGowers.DiscreteProduct
public import LpGowers.MonotoneApproximation
public import LpGowers.Scaling

/-! # Dimension-polynomial extension of a restricted estimate

A threshold halves the allowed size of the large-value set at each recursive
step. This is the dyadic argument in Proposition 8.1.
-/

@[expose] public section
noncomputable section
open scoped NNReal BigOperators

namespace LpGowers.Discrete

/-- An abstract positive, monotone, subadditive, 1-homogeneous functional obeying
an indicator bound admits a bound with logarithmic loss in the number of points. -/
theorem dyadic_extension {X : Type*} [DecidableEq X] (Ω : Finset X)
    (F : (X → ℝ≥0) → ℝ≥0) (q : ℝ) (hq : 0 < q)
    (hmono : Monotone F) (hadd : ∀ a b, F (a+b) ≤ F a + F b)
    (hscale : ∀ (c : ℝ≥0) f, F (fun x => c*f x) = c*F f)
    (hset : ∀ A : Finset X, A ⊆ Ω →
      F (fun x => if x ∈ A then 1 else 0) ≤ (A.card : ℝ≥0) ^ (1/q)) (K : ℕ)
    (A : Finset X) (hA : A ⊆ Ω) (hcard : A.card ≤ 2^K) (f : X → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) (M : ℝ≥0)
    (hmass : ∑ x ∈ A, f x ^ q ≤ M ^ q) :
    F f ≤ (K + 1 : ℕ) * (2 : ℝ≥0) ^ (1/q) * M := by
  classical
  have fbound (x : X) : f x ≤ M := by
    by_cases hx : x ∈ A
    · apply (NNReal.rpow_le_rpow_iff hq).mp
      exact (Finset.single_le_sum (fun _ _ => zero_le) hx).trans hmass
    · simp [hf x hx]
  by_cases hzero : M = 0
  · subst M
    have hf0 : f = 0 := funext (fun x => le_antisymm (fbound x) zero_le)
    have hh := hscale 0 (0 : X → ℝ≥0)
    simpa [hf0, Pi.zero_def] using hh.le
  have hM : 0 < M := lt_of_le_of_ne zero_le (Ne.symm hzero)
  have hq' : 0 < 1/q := one_div_pos.mpr hq
  induction K generalizing A f with
  | zero =>
    have hsmall : (A.card : ℝ≥0) ^ (1/q) ≤ 1 := by
      simpa using NNReal.rpow_le_rpow (show (A.card : ℝ≥0) ≤ 1 by exact_mod_cast hcard) hq'.le
    have hr : 1 ≤ (2 : ℝ≥0) ^ (1/q) := by
      simpa using NNReal.rpow_le_rpow (by norm_num : (1 : ℝ≥0) ≤ 2) hq'.le
    calc
      F f ≤ F (fun x => M * (if x ∈ A then 1 else 0)) := by
        apply hmono
        intro x
        by_cases hx : x ∈ A <;> simp [hx, hf, fbound]
      _ ≤ M * 1 := by rw [hscale]; gcongr; exact (hset A hA).trans hsmall
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hr zero_le
  | succ K ih =>
    let N : ℝ≥0 := 2 ^ K
    have hN : 0 < N := by dsimp [N]; positivity
    let a := M / N^(1/q)
    let B := A.filter fun x => a < f x
    let g (x : X) := if x ∈ B then f x else 0
    have hB : B ⊆ A := Finset.filter_subset _ _
    have ha : 0 < a := div_pos hM (NNReal.rpow_pos hN)
    have hapow : a^q = M^q / N := by rw [NNReal.div_rpow]; simp [one_div, hq.ne']
    have hcardB : B.card ≤ 2^K := by
      have hh : (B.card : ℝ≥0) * a^q ≤ M^q := calc
        _ = ∑ _ ∈ B, a^q := by simp
        _ ≤ ∑ x ∈ B, f x ^ q := Finset.sum_le_sum fun x hx =>
          NNReal.rpow_le_rpow (Finset.mem_filter.mp hx).2.le hq.le
        _ ≤ ∑ x ∈ A, f x ^ q := Finset.sum_le_sum_of_subset hB
        _ ≤ M^q := hmass
      rw [hapow, ← mul_div_assoc, div_le_iff₀ hN] at hh
      have hMp : 0 < M^q := NNReal.rpow_pos hM
      have hn' : (B.card : ℝ≥0) ≤ N := (le_of_mul_le_mul_right (by simpa [mul_comm] using hh) hMp)
      dsimp [N] at hn'
      exact_mod_cast hn'
    have hmassB : ∑ x ∈ B, g x ^ q ≤ M^q := by
      have hs : ∑ x ∈ B, g x ^ q = ∑ x ∈ B, f x ^ q :=
        Finset.sum_congr rfl fun x hx => by simp [g, hx]
      rw [hs]
      exact (Finset.sum_le_sum_of_subset hB).trans hmass
    have hsmall := ih B (hB.trans hA) hcardB g (fun x hx => by simp [g,hx]) hmassB
      (fun x => by by_cases hx : x ∈ B <;> simp [g,hx,fbound])
    have hcost : a * (A.card : ℝ≥0) ^ (1/q) ≤ (2 : ℝ≥0)^(1/q) * M := calc
      _ ≤ a * (2 * N)^(1/q) := by
        gcongr
        dsimp [N]
        exact_mod_cast (show A.card ≤ 2*(2^K) by simpa [pow_succ, Nat.mul_comm] using hcard)
      _ = _ := by
        rw [NNReal.mul_rpow]
        dsimp [a]
        field_simp [(NNReal.rpow_pos (p := 1/q) hN).ne']
    calc
      F f ≤ F (g + (fun x => a * (if x ∈ A then 1 else 0))) := by
        apply hmono
        intro x
        by_cases hx : x ∈ A
        · by_cases hb : x ∈ B
          · simp [g,Pi.add_apply,hb,hx]
          · have hval : f x ≤ a := by simpa [B, hx] using hb
            simpa [g,Pi.add_apply,hb,hx] using hval
        · have hb : x ∉ B := fun h => hx (hB h)
          simp [g,Pi.add_apply,hb,hx,hf x hx]
      _ ≤ F g + F (fun x => a * (if x ∈ A then 1 else 0)) := hadd _ _
      _ ≤ (K + 1 : ℕ) * (2 : ℝ≥0)^(1/q)*M + (2:ℝ≥0)^(1/q)*M := by
        rw [hscale]
        exact add_le_add hsmall ((mul_le_mul_of_nonneg_left (hset A hA) zero_le).trans hcost)
      _ = _ := by push_cast; ring


open MeasureTheory
open scoped ENNReal

/-- The restricted-set hypothesis of Proposition 8.1 yields the sharp weighted
bound as soon as the triangle inequality of Appendix A is available on the cubes. -/
theorem functionExponent_of_setExponent_of_triangle (d k n : ℕ) (q : ℝ) (hq : 0 < q)
    (hset : (2:ℝ)^d * (k+1:ℕ) / q ∈ setExponents d (k+1) n)
    (htri : ∀ (m : ℕ) (f g : Lattice m → ℝ≥0), (∀ x, x ∉ box m n → f x = 0) →
      (∀ x, x ∉ box m n → g x = 0) →
      gowers Measure.count d (k+1:ℕ) (f+g) ≤
      gowers Measure.count d (k+1:ℕ) f + gowers Measure.count d (k+1:ℕ) g) :
    q ∈ functionExponents d (k+1) n := by
  let V : ℕ := 2^d * (k+1)
  have hV : 0 < (V : ℝ) := by dsimp [V]; positivity
  let D : ℝ≥0 := (n+1:ℕ) * (2:ℝ≥0)^(1/q)
  apply functionExponent_of_polynomial_loss d k n hq ((D:ℝ)^V) (by dsimp [D]; positivity) V
  intro m f hf
  let B := box m n
  let clip (g : Lattice m → ℝ≥0) (x : Lattice m) := if x ∈ B then g x else 0
  let F (g : Lattice m → ℝ≥0) := weightedEnergy d (k+1) B (clip g) ^ (1/(V:ℝ))
  have hsupp (g : Lattice m → ℝ≥0) : ∀ x, x ∉ B → clip g x = 0 := fun x hx => by simp [clip, hx]
  have hc (g : Lattice m → ℝ≥0) : (F g : ℝ≥0∞) = gowers Measure.count d (k+1:ℕ) (clip g) := by
    rw [gowers_eq_weightedEnergy d k B (clip g) (hsupp g)]
    simp [F,V]
    exact ENNReal.coe_rpow_of_nonneg _ (by positivity)
  have hmono : Monotone F := by
    intro a b hab
    apply ENNReal.coe_le_coe.mp
    rw [hc, hc]
    apply gowers_mono _ _ _ (by positivity)
    intro x
    by_cases hx : x ∈ B <;> simp [clip,hx,hab x]
  have hadd (a b : Lattice m → ℝ≥0) : F (a+b) ≤ F a + F b := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_add, hc,hc,hc]
    have he : clip (a+b) = clip a + clip b := by
      funext x; by_cases hx : x ∈ B <;> simp [clip, hx]
    rw [he]
    exact htri _ _ _ (hsupp a) (hsupp b)
  have hscale (c : ℝ≥0) (g : Lattice m → ℝ≥0) : F (fun x => c*g x) = c*F g := by
    apply ENNReal.coe_injective
    rw [ENNReal.coe_mul, hc, hc]
    have he : clip (fun x => c*g x) = fun x => c*clip g x := by
      funext x; by_cases hx : x ∈ B <;> simp [clip, hx]
    rw [he, gowers_smul_input _ _ _ _ (by positivity)]
  have hI (A : Finset (Lattice m)) (hA : A ⊆ B) :
      F (fun x => if x ∈ A then 1 else 0) ≤ (A.card:ℝ≥0)^(1/q) := by
    apply ENNReal.coe_le_coe.mp
    rw [hc]
    have he : clip (fun x => if x ∈ A then 1 else 0) = finIndicator A := by
      funext x
      by_cases hx : x ∈ A
      · simp [clip, finIndicator, hx, hA hx]
      · simp [clip, finIndicator, hx]
    rw [he, gowers_finIndicator]
    have hE : (energy d (k+1) A : ℝ≥0) ≤ (A.card : ℝ≥0)^((V:ℝ)/q) := by
      exact_mod_cast (by simpa [V] using hset.2 m A hA :
        (energy d (k+1) A : ℝ) ≤ (A.card : ℝ)^((V:ℝ)/q))
    have hR := NNReal.rpow_le_rpow hE (one_div_nonneg.mpr hV.le)
    rw [← NNReal.rpow_mul, show (V:ℝ)/q * (1/(V:ℝ)) = 1/q by field_simp] at hR
    change (↑(energy d (k+1) A) : ℝ≥0∞) ^ _ ≤ _
    convert ENNReal.coe_le_coe.mpr hR using 1
    simp [V]
    exact (ENNReal.coe_rpow_of_nonneg _ (by positivity)).symm
  let Z := ∑ x ∈ B, f x ^ q
  let L := Z^(1/q)
  have hcard : B.card ≤ 2^(n*m) := by
    rw [card_box, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
  have hm : ∑ x ∈ B, f x ^ q ≤ L^q := by
    change Z ≤ (Z^(1/q))^q
    simp [one_div, hq.ne']
  have hlo := dyadic_extension B F q hq hmono hadd hscale hI (n*m) B (Finset.Subset.refl _) hcard f hf L hm
  have hclip : clip f = f := by
    funext x
    by_cases hx : x ∈ B
    · simp [clip,hx]
    · simpa [clip,hx] using (hf x hx).symm
  have hbig : F f ≤ D * ((m:ℝ≥0)+1) * L := by
    refine hlo.trans ?_
    dsimp [D]
    have hn : ((n*m+1:ℕ):ℝ≥0) ≤ ((n+1:ℕ):ℝ≥0) * ((m:ℝ≥0)+1) := by
      exact_mod_cast (show n*m+1 ≤ (n+1)*(m+1) by nlinarith)
    calc
      _ ≤ (((n+1:ℕ):ℝ≥0)*((m:ℝ≥0)+1)) * (2:ℝ≥0)^(1/q)*L := by gcongr
      _ = _ := by ring
  have hpow := pow_le_pow_left' hbig V
  change (weightedEnergy d (k+1) B (clip f) ^ (1/(V:ℝ))) ^ V ≤ _ at hpow
  rw [hclip, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, one_div_mul_cancel hV.ne',
    NNReal.rpow_one, mul_pow, mul_pow] at hpow
  have hL : L^V = Z ^ ((V:ℝ)/q) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 1
    ring
  rw [hL] at hpow
  exact_mod_cast (by simpa [V,Z,B] using hpow)

/-- The critical product identity (1.12) follows from the integer-p triangle
inequality asserted in Appendix A on cube-supported functions. -/
theorem critical_product_of_triangle (d k n : ℕ) (hn : 2 ≤ n)
    (htri : ∀ (m : ℕ) (f g : Lattice m → ℝ≥0), (∀ x, x ∉ box m n → f x = 0) →
      (∀ x, x ∉ box m n → g x = 0) →
      gowers Measure.count d (k+1:ℕ) (f+g) ≤
      gowers Measure.count d (k+1:ℕ) f + gowers Measure.count d (k+1:ℕ) g) :
    criticalQ d (k+1) n * criticalT d (k+1) n = (2:ℝ)^d*(k+1:ℕ) := by
  refine le_antisymm (criticalQ_mul_criticalT_le d k n hn) ?_
  let t := criticalT d (k+1) n
  let v : ℝ := 2^d * (k+1:ℕ)
  have hmin := (criticalT_isLeast d k n hn).1
  have ht : 0 < t := hmin.1
  have hv : 0 < v := by dsimp [v]; positivity
  have hmem : v / (v / t) ∈ setExponents d (k+1) n := by simpa [hv.ne'] using hmin
  have hq := functionExponent_of_setExponent_of_triangle d k n (v/t) (div_pos hv ht) hmem htri
  exact (div_le_iff₀ ht).mp ((criticalQ_isGreatest d k n hn).2 hq)

end LpGowers.Discrete
