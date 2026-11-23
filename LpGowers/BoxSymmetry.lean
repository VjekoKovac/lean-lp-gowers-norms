module

public import LpGowers.CubeSymmetry
public import LpGowers.TensorTransfer
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Identifying the sizes of the sides of a symmetric box

A box close to a permutation-invariant density overlaps each transposed box
in all but a small part of its mass. Comparing that intersection to the box
with one side replaced bounds every ratio of side masses. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LpGowers

/-- A positive finite product forces each side of the box to have positive
finite measure, including when the ambient measure is infinite. -/
theorem box_sides_finite {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} (A : Fin n → Set X) (h0 : (cubeMeasure μ n) (univ.pi A) ≠ 0)
    (ht : (cubeMeasure μ n) (univ.pi A) ≠ ⊤) (i : Fin n) :
    μ (A i) ≠ 0 ∧ μ (A i) ≠ ⊤ := by
  classical
  have he := Measure.pi_pi (fun _ : Fin n => μ) A
  change _ = ∏ i, μ (A i) at he
  have h0' : (∏ i, μ (A i)) ≠ 0 := he.symm.trans_ne h0
  have ht' : (∏ i, μ (A i)) ≠ ⊤ := he.symm.trans_ne ht
  have nz (j) : μ (A j) ≠ 0 := Finset.prod_ne_zero_iff.mp h0' j (Finset.mem_univ j)
  refine ⟨nz i,?_⟩
  intro h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), h,
    ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr (fun j _ => nz j))] at ht'
  exact ht' rfl

/-- The overlap with the transposition of coordinates `i` and `j` bounds
the mass of side `i` in terms of side `j`. -/
theorem box_side_comparison {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} (F : (Fin n → X) → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, F (x ∘ σ) = F x)
    (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i))
    (h0 : (cubeMeasure μ n) (univ.pi A) ≠ 0) (ht : (cubeMeasure μ n) (univ.pi A) ≠ ⊤)
    {κ : ℝ} (hk : 0 ≤ κ) (hnear : l1DensityError (cubeMeasure μ n) F ((univ.pi A).indicator 1) ≤ ENNReal.ofReal κ)
    (i j : Fin n) :
    μ.real (A i) * ((cubeMeasure μ n).real (univ.pi A) - 2*κ) ≤
      μ.real (A j) * (cubeMeasure μ n).real (univ.pi A) := by
  classical
  let ν := cubeMeasure μ n
  let B := univ.pi A
  let σ := Equiv.swap i j
  let T := fun x : Fin n → X => x ∘ σ
  let B' := T ⁻¹' B
  let I := fun (U : Set (Fin n → X)) => U.indicator (1 : (Fin n → X) → ℝ≥0∞)
  have mT : MeasurePreserving T ν ν := cubeMeasure_perm μ σ
  have mB : MeasurableSet B := MeasurableSet.univ_pi hA
  have mB' : MeasurableSet B' := mT.measurable mB
  have hswap : l1DensityError ν F (I B') = l1DensityError ν F (I B) := by
    let D := fun x => (F x-I B x)+(I B x-F x)
    have hm : Measurable D := (hF.sub (measurable_const.indicator mB)).add ((measurable_const.indicator mB).sub hF)
    apply Eq.trans _ (mT.lintegral_comp hm)
    apply lintegral_congr
    intro x
    have hi : I B' x = I B (T x) := by
      by_cases h : T x ∈ B
      · have hx : x ∈ B' := h
        simp [I,h,hx]
      · have hx : x ∉ B' := h
        simp [I,h,hx]
    change (F x-I B' x)+(I B' x-F x) = (F (T x)-I B (T x))+(I B (T x)-F (T x))
    rw [hi,hsym σ x]
  have hclose : l1DensityError ν (I B) (I B') ≤ ENNReal.ofReal κ + ENNReal.ofReal κ := by
    apply (l1DensityError_triangle ν (F := I B) (G := F) (H := I B') (measurable_const.indicator mB) hF (measurable_const.indicator mB')).trans
    rw [hswap]
    exact add_le_add ((lintegral_congr (fun x => add_comm _ _)).le.trans hnear) hnear
  have hdiff : ν (B \ B') ≤ ENNReal.ofReal (2*κ) := by
    rw [← lintegral_indicator_one (mB.diff mB'), two_mul,ENNReal.ofReal_add hk hk]
    apply le_trans _ hclose
    apply lintegral_mono
    intro x
    by_cases h : x∈B <;> by_cases h' : x∈B' <;> simp [I,h,h']
  have hInt : ν.real B - 2*κ ≤ ν.real (B∩B') := by
    have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdiff
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*κ)] at H
    have he := measureReal_sdiff_add_inter (μ := ν) (s := B) mB' ht
    change ν.real (B \ B') ≤ 2*κ at H
    linarith
  let C := univ.pi (Function.update A i (A j))
  have hsub : B∩B' ⊆ C := by
    intro x hx
    apply mem_univ_pi.mpr
    intro m
    by_cases hi : m=i
    · subst m
      have ha := (mem_univ_pi.mp (show T x ∈ B from hx.2)) j
      simpa [T,σ,Function.comp_def] using ha
    · simpa [Function.update_of_ne hi] using mem_univ_pi.mp hx.1 m
  have hside := box_sides_finite μ A h0 ht
  have hc' (m) : μ (Function.update A i (A j) m) ≠ ⊤ := by
    by_cases h : m=i <;> simp [h,Function.update_of_ne,hside]
  have hfinite : ν C ≠ ⊤ := (Measure.pi_pi (fun _ : Fin n => μ) _).trans_ne
    (ENNReal.prod_ne_top fun m _ => hc' m)
  have hS : μ.real (A i) * ν.real C = μ.real (A j) * ν.real B := by
    let m := fun i => μ.real (A i)
    have eqC : ν.real C = ∏ t, Function.update m i (m j) t := by
      rw [measureReal_def, show ν C = ∏ t, μ (Function.update A i (A j) t) from Measure.pi_pi _ _, ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro t _
      by_cases h : t=i <;> simp [m,h,Function.update_of_ne,measureReal_def]
    have eqB : ν.real B = ∏ t, m t := by
      rw [measureReal_def, show ν B = ∏ t, μ (A t) from Measure.pi_pi _ _, ENNReal.toReal_prod]
      rfl
    rw [eqC,eqB,Finset.prod_update_of_mem (Finset.mem_univ i), ← Finset.mul_prod_erase _ m (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase,m]
    ac_rfl
  exact (mul_le_mul_of_nonneg_left (hInt.trans (measureReal_mono hsub hfinite)) measureReal_nonneg).trans_eq hS

/-- A box of mass close to one that approximates a symmetric density has
every side close to unit mass. The same tolerance works in all positive
dimensions and for every sigma-finite factor measure. -/
theorem symmetric_box_sides {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (n : ℕ) (F : (Fin (n+1) → X) → ℝ≥0∞), Measurable F →
      (∀ (σ : Equiv.Perm (Fin (n+1))) x, F (x ∘ σ) = F x) →
      ∀ A : Fin (n+1) → Set X, (∀ i, MeasurableSet (A i)) →
      |(cubeMeasure μ (n+1)).real (univ.pi A) - 1| ≤ δ →
      l1DensityError (cubeMeasure μ (n+1)) F ((univ.pi A).indicator 1) ≤ ENNReal.ofReal δ →
      ∀ i, μ (A i) ≠ 0 ∧ μ (A i) ≠ ⊤ ∧ |μ.real (A i)-1| ≤ η := by
  let δ := min (1/8) (η/10)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd₁ : δ ≤ 1/8 := min_le_left _ _
  have hdη : 10*δ ≤ η := by linarith only [show δ ≤ η/10 from min_le_right _ _]
  refine ⟨δ,hd,?_⟩
  intro X _ μ _ n F hF hFσ A hA hv hnear
  let V := (cubeMeasure μ (n+1)).real (univ.pi A)
  let m := fun i => μ.real (A i)
  have hrange : -δ ≤ V-1 ∧ V-1 ≤ δ := abs_le.mp hv
  have hV : 0 < V := by linarith
  have hVr := ENNReal.toReal_pos_iff.mp hV
  have hside := box_sides_finite μ A hVr.1.ne' hVr.2.ne
  have hm i : 0 < m i := ENNReal.toReal_pos (hside i).1 (hside i).2
  have hprod : V = ∏ i, m i := by
    dsimp only [V, m, measureReal_def]
    rw [show (cubeMeasure μ (n+1)) (univ.pi A) = ∏ i, μ (A i) from Measure.pi_pi _ _,
      ENNReal.toReal_prod]
  have pair (i j : Fin (n+1)) : (1-4*δ)*m i ≤ m j := by
    have H := box_side_comparison μ F hF hFσ A hA hVr.1.ne' hVr.2.ne hd.le hnear i j
    change m i * (V-2*δ) ≤ m j * V at H
    have hK : (1-4*δ)*V ≤ V-2*δ := by
      nlinarith [mul_nonneg hd.le (show 0 ≤ V-1/2 by linarith)]
    apply le_of_mul_le_mul_right (a := V) _ hV
    nlinarith only [mul_le_mul_of_nonneg_left hK (hm i).le, H]
  have hup : ∃ i, m i ≤ 1+δ := by
    by_contra! bad
    have H := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := fun _ : Fin (n+1) => 1+δ)
      (fun _ _ => by linarith) (fun i _ => bad i) Finset.univ_nonempty
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← hprod,pow_succ] at H
    have h₁ := one_le_pow₀ (n := n) (show 1 ≤ 1+δ by linarith)
    nlinarith only [H,mul_le_mul_of_nonneg_right h₁ (show 0 ≤ 1+δ by linarith),hrange.2]
  have hlow : ∃ i, 1-δ ≤ m i := by
    by_contra! bad
    have H := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (fun i _ => hm i)
      (fun i _ => bad i) Finset.univ_nonempty
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← hprod,pow_succ] at H
    have h₁ := pow_le_one₀ (n := n) (show 0 ≤ 1-δ by linarith) (show 1-δ ≤ 1 by linarith)
    nlinarith only [H,mul_le_mul_of_nonneg_right h₁ (show 0 ≤ 1-δ by linarith),hrange.1]
  obtain ⟨u,hu⟩ := hup
  obtain ⟨l,hl⟩ := hlow
  have hk : 0 < 1-4*δ := by linarith
  intro i
  refine ⟨(hside i).1,(hside i).2,abs_le.mpr ⟨?_,?_⟩⟩
  · nlinarith only [(mul_le_mul_of_nonneg_left hl hk.le).trans (pair l i), hd.le, sq_nonneg δ, hdη]
  · have H : (1-4*δ) * m i ≤ 1+δ := (pair i u).trans hu
    have cmp : 1+δ ≤ (1-4*δ)*(1+10*δ) := by
      nlinarith only [mul_nonneg hd.le (show 0 ≤ 1-8*δ by linarith)]
    have hfinal := le_of_mul_le_mul_left (H.trans cmp) hk
    linarith

end LpGowers
