module

public import LpGowers.DegreeNear
import Mathlib.Tactic

/-! # Near equality in reverse degree lowering

In the reverse regime the stabilized Hölder product contains the normalized
joint density and the full (possibly subnormalized) Loomis–Whitney product
among its factors. Its integral is bounded below by a fixed positive power
of the near-extremizer ratio, as in §5 of Kovač–Rogers. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers

private lemma reverse_mass_identity {j : ℕ} {p : ℝ} {q θ : Fin (j+2) → ℝ}
    (h : DegreeParameters (j+1) p q θ) (hR : DegreeReverse p θ)
    (N : Fin (j+2) → ℝ≥0∞) (hn : ∀ i, N i ≠ 0 ∧ N i ≠ ⊤) :
    (∏ i, N i ^ (2*p*θ i/q i)) ^ (1/(θ 0*p)) *
      ((∏ i, N i ^ (1/((j:ℝ)+1))) ^ ((p-1)/(θ 0*p)) *
        ∏ t : Fin (j+1), N t.succ ^ (-(θ t.succ)/(θ 0))) = N 0 := by
  let r := 1/((j:ℝ)+1)
  let a := 1/(θ 0*p)
  let c := (p-1)/(θ 0*p)
  let e := fun i => 2*p*θ i/q i
  let b := fun t : Fin (j+1) => -(θ t.succ)/(θ 0)
  have hp : 0 < p := zero_lt_one.trans hR.1
  have ht : 0 < θ 0 := hR.2.1
  have ha : 0 < a := one_div_pos.mpr (mul_pos ht hp)
  have hc : 0 < c := div_pos (sub_pos.mpr hR.1) (mul_pos ht hp)
  have hj : 0 < (j:ℝ)+1 := by positivity
  have he (i) : e i*a + r*c = θ i/(θ 0) := by
    have H := h.2.2 i
    change (1-1/p) / ((j+1:ℕ):ℝ) = θ i*(1-2/q i) at H
    push_cast at H
    dsimp [e,a,r,c]
    field_simp [hp.ne',ht.ne',hj.ne',(h.1 i).ne'] at H ⊢
    nlinarith only [H]
  change (∏ i, N i ^ e i)^a * ((∏ i,N i^r)^c * ∏ t, N t.succ ^ b t) = _
  rw [← mul_assoc, ← ENNReal.prod_rpow_of_nonneg ha.le, ← ENNReal.prod_rpow_of_nonneg hc.le,
    ← Finset.prod_mul_distrib]
  simp_rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (hn _).1 (hn _).2, he]
  rw [Fin.prod_univ_succ, div_self ht.ne', ENNReal.rpow_one, mul_assoc, ← Finset.prod_mul_distrib]
  simp [b, ← ENNReal.rpow_add _ _ (hn _).1 (hn _).2, neg_div]

/-- Reverse-regime proximity of the normalized joint density and normalized
deletion-face product, with a threshold independent of the group. -/
theorem degree_reverse_near (j : ℕ) {p : ℝ} {q θ : Fin (j+2) → ℝ}
    (hpar : DegreeParameters (j+1) p q θ) (hrev : DegreeReverse p θ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ (G : Type*) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
      (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ] (f : G → ℝ≥0),
    AEMeasurable f μ → (0 < gowers μ (j+2) p f ∧ gowers μ (j+2) p f < ⊤) →
    (∀ i, 0 < gowers μ (j+1) (q i) f ∧ gowers μ (j+1) (q i) f < ⊤) →
    ENNReal.ofReal (1-ε) * gowers μ (j+2) p f ≤ lowerProduct μ (j+1) q θ f →
    jointFaceError μ j p q f ≤ ENNReal.ofReal η := by
  let a := 1/(θ 0*p)
  let c := (p-1)/(θ 0*p)
  let b := fun i : Fin (j+1) => -(θ i.succ)/(θ 0)
  let r := 1/((j:ℝ)+1)
  let t := (2:ℝ)^(j+2)*p
  let γ : Fin (j+3) → ℝ := Fin.cons c (Fin.cons a b)
  have hp : 0 < p := zero_lt_one.trans hrev.1
  have hθ : 0 < θ 0 := hrev.2.1
  have ha : 0 < a := one_div_pos.mpr (mul_pos hθ hp)
  have hc : 0 < c := div_pos (sub_pos.mpr hrev.1) (mul_pos hθ hp)
  have hb (i) : 0 < b i := div_pos (neg_pos.mpr (hrev.2.2 i)) hθ
  have hr : 0 < r := by dsimp [r]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hγ (i) : 0 < γ i := Fin.cases hc (fun i => Fin.cases ha hb i) i
  have hbSum : ∑ i, b i = (θ 0-1)/(θ 0) := by
    have H := hpar.2.1
    rw [Fin.sum_univ_succ] at H
    dsimp only [b]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    congr 1
    linarith
  have hsum : ∑ i, γ i = 1 := by
    calc
      _ = c + (a + ∑ i, b i) := by
        rw [Fin.sum_univ_succ]; congr 1
        rw [Fin.sum_univ_succ]; rfl
      _ = 1 := by rw [hbSum]; dsimp [a,c]; field_simp; ring
  obtain ⟨D,hD,HH⟩ := holder_stability_ennreal γ hγ hsum hη
  obtain ⟨δ,hd,_,Hδ⟩ := small_power_deficit (t*a) (half_pos hD)
  refine ⟨δ,hd,?_⟩
  intro ε hε hεδ G _ _ _ μ _ _ f hf hJ hI hnear
  let F := autocorrelation μ (j+2) f
  let M := autocorrelation μ (j+1) f
  let ν := cubeMeasure μ (j+2)
  let ξ := cubeMeasure μ (j+1)
  let U := ∫⁻ x, F x ^ p ∂ν
  let N := fun i => ∫⁻ y, M y ^ q i ∂ξ
  let T := fun (i : Fin (j+2)) x => F x * M (deleteCoord i x) ^ (q i-2)
  let V := fun x => ∏ i, (M (deleteCoord i x) ^ q i)^r
  let L := ∏ i, N i ^ r
  let A : Fin (j+3) → (Fin (j+2) → G) → ℝ≥0∞ :=
    Fin.cons V (Fin.cons (fun x => F x^p) (fun i : Fin (j+1) => T i.succ))
  let Z : Fin (j+3) → ℝ≥0∞ := Fin.cons L (Fin.cons U (fun i : Fin (j+1) => N i.succ))
  let u := fun i x => A i x / Z i
  let K := ∏ i, Z i ^ γ i
  have hF : Measurable F := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hM : Measurable M := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hu : U ≠ 0 ∧ U ≠ ⊤ := moment_regular_of_gowers μ _ hp hJ
  have hn i : N i ≠ 0 ∧ N i ≠ ⊤ := moment_regular_of_gowers μ _ (hpar.1 i) (hI i)
  have hL : L ≠ 0 ∧ L ≠ ⊤ :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (hn i).1) (hn i).2).ne'),
      ENNReal.prod_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hn i).1 (hn i).2)⟩
  have hz i : Z i ≠ 0 ∧ Z i ≠ ⊤ := Fin.cases hL (fun i => Fin.cases hu (fun i => hn i.succ) i) i
  have hK : K ≠ 0 ∧ K ≠ ⊤ :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (hz i).1) (hz i).2).ne'),
      ENNReal.prod_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hz i).1 (hz i).2)⟩
  have hT i : Measurable (T i) := hF.mul ((hM.comp (measurable_omitCoord i)).pow_const _)
  have hV : Measurable V := lwProduct_measurable (fun i => hM.pow_const (q i))
  have hA i : Measurable (A i) := Fin.cases hV (fun i => Fin.cases (hF.pow_const p) (fun i => hT i.succ) i) i
  have humeas i : Measurable (u i) := (hA i).div_const _
  have hraw (i) : (∫⁻ x, A i x ∂ν) ≤ Z i := by
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun m => ?_) i) i
    · exact functionalLoomisWhitney μ j (fun i x => M x ^ q i) (fun i => hM.pow_const _)
    · exact le_rfl
    · exact (tilted_marginal_integral μ m.succ hF hM (hpar.1 _) (hn _).2
        (autocorrelation_marginal μ hf (j+1) _)).le
  have humass i : (∫⁻ x, u i x ∂ν) ≤ 1 := by
    simp only [u, div_eq_mul_inv, lintegral_mul_const _ (hA i)]
    exact (mul_le_mul_left (hraw i) _).trans_eq (ENNReal.mul_inv_cancel (hz i).1 (hz i).2)
  have hN0 : N 0 ≤ ∫⁻ x, ∏ i, A i x ^ γ i ∂ν := by
    have H := reverse_raw_product_mass μ j hpar hrev hF hM (fun i => (hn i).2)
      (autocorrelation_marginal μ hf (j+1))
    simpa only [A,γ,Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,ν,a,c,b,T,M,F,V,N,ξ,r] using H
  let E := ENNReal.ofReal (1-ε)
  let P := ∏ i, N i^(2*p*θ i/q i)
  have hEU : E^t * U ≤ P := by
    obtain ⟨hw,hv⟩ := degree_moment_conversion μ (j+1) hp q θ hpar.1 f
    have H := ENNReal.rpow_le_rpow hnear ht.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,hw,hv] at H
    exact H
  let J := L^c * ∏ m : Fin (j+1), N m.succ ^ b m
  have hEK : E^(t*a)*K ≤ N 0 := by
    have he := ENNReal.rpow_le_rpow hEU ha.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le, ← ENNReal.rpow_mul] at he
    have hJK : K = U^a * J := by
      simp only [K, J, Z, γ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ac_rfl
    rw [hJK, ← mul_assoc]
    exact (mul_le_mul_left he J).trans_eq (reverse_mass_identity hpar hrev N hn)
  have hm : Measurable (fun x => ∏ i, A i x ^ γ i) :=
    Finset.measurable_prod _ (fun i _ => (hA i).pow_const _)
  have hprod (x) : (∏ i, u i x ^ γ i) = (∏ i, A i x ^ γ i) / K := by
    simp only [u,K,ENNReal.div_rpow_of_nonneg _ _ (hγ _).le]
    exact ENNReal.prod_div_distrib_of_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hz i).1 (hz i).2)
  have hlower : ENNReal.ofReal (1-D/2) ≤ ∫⁻ x, ∏ i, u i x ^ γ i ∂ν := by
    simp_rw [hprod, div_eq_mul_inv, lintegral_mul_const _ hm]
    apply (Hδ ε hε.le hεδ).trans
    exact (ENNReal.le_div_iff_mul_le (Or.inl hK.1) (Or.inl hK.2)).mpr (hEK.trans hN0)
  have H := (HH (D/2) (half_pos hD).le (half_lt_self hD) ν u
    (fun i => (humeas i).aemeasurable) humass hlower (0 : Fin (j+2)).succ).2 0
  have hU0 : u 0 = lwProduct j (fun i => momentDensity ξ (q i) M) := by
    funext x
    change (∏ i, (M (deleteCoord i x)^q i)^r) / L = ∏ i, (M (deleteCoord i x)^q i / N i)^r
    simp_rw [ENNReal.div_rpow_of_nonneg _ _ hr.le]
    exact (ENNReal.prod_div_distrib_of_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hn i).1 (hn i).2)).symm
  rw [hU0] at H
  exact H

end LpGowers
