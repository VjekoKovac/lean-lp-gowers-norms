module

public import LpGowers.WeightedDegree
public import LpGowers.ReverseAlgebra
public import LpGowers.Nonvanishing

/-! # The reverse degree-lowering inequality

For a positive exponent `p>1`, isolate the unique positive weight. In this
form all weights in the application of Hölder's inequality are nonnegative.
The normalized Loomis–Whitney factor controls the missing density. -/

public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

/-- Pointwise reverse Hölder factorization on the positive finite marginal support. -/
theorem reverse_pointwise {n : ℕ} (p a c r : ℝ) (q : Fin (n+1) → ℝ) (b : Fin n → ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : ∀ i, 0 ≤ b i)
    (hs : p*a + ∑ i, b i = 1) (hp : 0 < p)
    (he₀ : q 0*r*c = q 0-2) (he : ∀ j, q j.succ*r*c + (q j.succ-2)*b j = 0)
    (z : ℝ≥0∞) (m : Fin (n+1) → ℝ≥0∞) (hm : ∀ i, m i ≠ 0 ∧ m i ≠ ⊤) :
    (∏ i, (m i ^ q i) ^ r) ^ c *
      ((z ^ p) ^ a * ∏ j : Fin n, (z * m j.succ ^ (q j.succ-2)) ^ b j) = z * m 0 ^ (q 0-2) := by
  rw [← ENNReal.prod_rpow_of_nonneg hc]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (hb _), ← ENNReal.rpow_mul]
  rw [Fin.prod_univ_succ, he₀, Finset.prod_mul_distrib]
  let V := fun j : Fin n => m j.succ ^ (q j.succ*r*c)
  let W := fun j : Fin n => m j.succ ^ ((q j.succ-2)*b j)
  change m 0 ^ (q 0-2) * (∏ j, V j) * (z ^ (p*a) * ((∏ j, z ^ (b j)) * ∏ j, W j)) = _
  have hVW : (∏ j, V j) * (∏ j, W j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [V, W, ← ENNReal.rpow_add _ _ (hm _).1 (hm _).2, he]
  calc
    _ = (z ^ (p*a) * ∏ j, z ^ (b j)) * m 0 ^ (q 0-2) * ((∏ j, V j) * ∏ j, W j) := by ac_rfl
    _ = _ := by
      rw [hVW, mul_one, prod_const_rpow_of_nonneg _ _ _ hb,
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp.le ha) (Finset.sum_nonneg (fun j _ => hb j)),
        hs, ENNReal.rpow_one]

/-- The joint marginal identity integrates the tilted density to its exact mass,
including the cases where the cube marginal vanishes. -/
theorem tilted_marginal_integral {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] {k : ℕ} (i : Fin (k+1))
    {F : (Fin (k+1) → G) → ℝ≥0∞} {M : (Fin k → G) → ℝ≥0∞}
    (hF : Measurable F) (hM : Measurable M) {q : ℝ} (hq : 0 < q)
    (hN : (∫⁻ y, M y ^ q ∂cubeMeasure μ k) ≠ ⊤)
    (hmarg : ∀ h, (∫⁻ a, F (i.insertNth a h) ∂μ) = M h ^ (2 : ℕ)) :
    (∫⁻ x, F x * M (deleteCoord i x) ^ (q-2) ∂cubeMeasure μ (k+1)) =
      ∫⁻ y, M y ^ q ∂cubeMeasure μ k := by
  rw [weighted_marginal μ i hF (hM.pow_const (q-2)) hmarg]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top (hM.pow_const q) hN] with y hy
  have hmt : M y ≠ ⊤ := by intro h; simp [h, ENNReal.top_rpow_of_pos hq] at hy
  by_cases hm0 : M y = 0
  · simp [hm0, ENNReal.zero_rpow_of_pos hq]
  · rw [← ENNReal.rpow_two, ← ENNReal.rpow_add _ _ hm0 hmt]
    simp

/-- The distinguished tilted marginal is bounded by the unnormalized
geometric mean before applying Hölder. Leaving the integral visible allows
one to apply the stability form of Hölder to exactly these factors. -/
theorem reverse_raw_product_mass {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] (j : ℕ) {p : ℝ} {q θ : Fin (j+2) → ℝ}
    (hpq : DegreeParameters (j+1) p q θ) (hrev : DegreeReverse p θ)
    {F : (Fin (j+2) → G) → ℝ≥0∞} {M : (Fin (j+1) → G) → ℝ≥0∞}
    (hF : Measurable F) (hM : Measurable M)
    (hN : ∀ i, (∫⁻ y, M y ^ (q i) ∂cubeMeasure μ (j+1)) ≠ ⊤)
    (hmarg : ∀ i : Fin (j+2), ∀ h, (∫⁻ a, F (i.insertNth a h) ∂μ) = M h ^ (2 : ℕ)) :
    let N := fun i => ∫⁻ y, M y ^ (q i) ∂cubeMeasure μ (j+1)
    let V := fun x => ∏ i, (M (deleteCoord i x) ^ q i) ^ (1/((j:ℝ)+1))
    let T := fun (i : Fin (j+2)) x => F x * M (deleteCoord i x) ^ (q i-2)
    N 0 ≤ ∫⁻ x, V x ^ ((p-1)/(θ 0*p)) * ((F x ^ p) ^ (1/(θ 0*p)) *
      ∏ t : Fin (j+1), T t.succ x ^ (-(θ t.succ)/(θ 0))) ∂cubeMeasure μ (j+2) := by
  let N := fun i => ∫⁻ y, M y ^ q i ∂cubeMeasure μ (j+1)
  let a := 1/(θ 0*p)
  let c := (p-1)/(θ 0*p)
  let b := fun t : Fin (j+1) => -(θ t.succ)/(θ 0)
  let r := 1/((j:ℝ)+1)
  obtain ⟨hq, hsumθ, hrel⟩ := hpq
  obtain ⟨hp1,hθ₀,hθ⟩ := hrev
  change 0 < θ 0 at hθ₀
  have hp : 0 < p := zero_lt_one.trans hp1
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := div_pos (by linarith) (mul_pos hθ₀ hp)
  have hb (i) : 0 < b i := div_pos (neg_pos.mpr (hθ i)) hθ₀
  have hbSum : (∑ i, b i) = (θ 0-1)/(θ 0) := by
    rw [Fin.sum_univ_succ] at hsumθ
    dsimp only [b]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    congr 1
    linarith
  have hsum : p*a + ∑ i, b i = 1 := by rw [hbSum]; dsimp [a]; field_simp; ring
  have hj : 0 < (j:ℝ) + 1 := by positivity
  have hcancel (i : Fin (j+2)) : q i*r*(p-1) = (q i-2)*(θ i*p) := by
    have he := hrel i
    norm_num only [Nat.cast_ofNat] at he
    push_cast at he
    dsimp [r]
    field_simp [hj.ne',hp.ne',(hq i).ne'] at he ⊢
    nlinarith only [he]
  have he₀ : q 0*r*c = q 0-2 := by dsimp [c]; rw [← mul_div_assoc, div_eq_iff (mul_pos hθ₀ hp).ne']; exact hcancel 0
  have he (t) : q t.succ*r*c + (q t.succ-2)*b t = 0 := by
    dsimp [b,c]
    field_simp [hθ₀.ne',hp.ne']
    nlinarith only [hcancel t.succ]
  let T := fun (i : Fin (j+2)) x => F x * M (deleteCoord i x) ^ (q i-2)
  let V := fun x => ∏ i, (M (deleteCoord i x) ^ (q i)) ^ r
  have hTmass (i) : (∫⁻ x, T i x ∂cubeMeasure μ (j+2)) = N i :=
    tilted_marginal_integral μ i hF hM (hq i) (hN i) (hmarg i)
  let A : Fin (j+2) → (Fin (j+2) → G) → ℝ≥0∞ := Fin.cons (fun x => F x ^ p) (fun i : Fin (j+1) => T i.succ)
  let w : Fin (j+2) → ℝ := Fin.cons a b
  have hall := ae_all_iff.mpr (fun i => finite_marginal_on_support μ i hF hM (hq i) (hN i) (hmarg i))
  have hpt : ∀ᵐ x ∂cubeMeasure μ (j+2), T 0 x ≤ V x ^ c * ∏ i, A i x ^ w i := by
    filter_upwards [hall] with x hx
    by_cases h0 : F x = 0
    · simp [T,h0]
    · apply le_of_eq
      rw [Fin.prod_univ_succ (fun i => A i x ^ w i)]
      simp only [A, w, Fin.cons_zero, Fin.cons_succ]
      exact (reverse_pointwise p a c r q b ha.le hc.le (fun t => (hb t).le) hsum hp he₀ he
        (F x) (fun i => M (deleteCoord i x)) (fun i => hx i h0)).symm
  apply (hTmass 0).symm.le.trans
  have h := lintegral_mono_ae hpt
  simpa only [T,V,pow_succ, r, b, a, c, N, Fin.prod_univ_succ, A, w, Fin.cons_zero, Fin.cons_succ] using h

/-- The weighted Hölder step in the reverse adjoint Loomis–Whitney argument.
The right side contains the high-order mass, the ordinary Loomis–Whitney
bound and the masses of all non-distinguished marginals. -/
theorem reverse_holder_marginals {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [SigmaFinite μ] (j : ℕ) {p : ℝ} {q θ : Fin (j+2) → ℝ}
    (hpq : DegreeParameters (j+1) p q θ) (hrev : DegreeReverse p θ)
    {F : (Fin (j+2) → G) → ℝ≥0∞} {M : (Fin (j+1) → G) → ℝ≥0∞}
    (hF : Measurable F) (hM : Measurable M)
    (hN : ∀ i, (∫⁻ y, M y ^ (q i) ∂cubeMeasure μ (j+1)) ≠ ⊤)
    (hmarg : ∀ i : Fin (j+2), ∀ h, (∫⁻ a, F (i.insertNth a h) ∂μ) = M h ^ (2 : ℕ)) :
    let N := fun i => ∫⁻ y, M y ^ (q i) ∂cubeMeasure μ (j+1)
    N 0 ≤ (∏ i, (N i) ^ (1/((j:ℝ)+1))) ^ ((p-1)/(θ 0*p)) *
      ((∫⁻ x, F x ^ p ∂cubeMeasure μ (j+2)) ^ (1/(θ 0*p)) *
        ∏ t : Fin (j+1), (N t.succ) ^ (-(θ t.succ)/(θ 0))) := by
  intro N
  let a := 1/(θ 0*p)
  let c := (p-1)/(θ 0*p)
  let b := fun t : Fin (j+1) => -(θ t.succ)/(θ 0)
  let r := 1/((j:ℝ)+1)
  obtain ⟨hq, hsumθ, hrel⟩ := hpq
  obtain ⟨hp1,hθ₀,hθ⟩ := hrev
  change 0 < θ 0 at hθ₀
  have hp : 0 < p := zero_lt_one.trans hp1
  have hr : 0 < r := by dsimp [r]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := div_pos (by linarith) (mul_pos hθ₀ hp)
  have hb (i) : 0 < b i := div_pos (neg_pos.mpr (hθ i)) hθ₀
  have hbSum : (∑ i, b i) = (θ 0-1)/(θ 0) := by
    rw [Fin.sum_univ_succ] at hsumθ
    dsimp only [b]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    congr 1
    linarith
  have hweights : c + (a + ∑ i, b i) = 1 := by rw [hbSum]; dsimp [a,c]; field_simp; ring
  let T := fun (i : Fin (j+2)) x => F x * M (deleteCoord i x) ^ (q i-2)
  let V := fun x => ∏ i, (M (deleteCoord i x) ^ (q i)) ^ r
  have hT (i) : Measurable (T i) := hF.mul ((hM.comp (measurable_omitCoord i)).pow_const _)
  have hV : Measurable V := Finset.measurable_prod _ (fun i _ => ((hM.comp (measurable_omitCoord i)).pow_const _).pow_const _)
  have hTmass (i) : (∫⁻ x, T i x ∂cubeMeasure μ (j+2)) = N i :=
    tilted_marginal_integral μ i hF hM (hq i) (hN i) (hmarg i)
  have hVmass : (∫⁻ x, V x ∂cubeMeasure μ (j+2)) ≤ ∏ i, (N i)^r :=
    functionalLoomisWhitney μ j (fun i y => M y ^ q i) (fun i => hM.pow_const _)
  let A : Fin (j+2) → (Fin (j+2) → G) → ℝ≥0∞ := Fin.cons (fun x => F x ^ p) (fun i : Fin (j+1) => T i.succ)
  let w : Fin (j+2) → ℝ := Fin.cons a b
  have hw : c + ∑ i, w i = 1 := by simpa [w,Fin.sum_univ_succ] using hweights
  have hw' (i) : 0 ≤ w i := Fin.cases ha.le (fun t => (hb t).le) i
  have hA (i) : Measurable (A i) := Fin.cases (hF.pow_const p) (fun t => hT t.succ) i
  have hld := ENNReal.lintegral_mul_prod_norm_pow_le (μ := cubeMeasure μ (j+2)) Finset.univ
    hV.aemeasurable (fun i _ => (hA i).aemeasurable) c hw hc.le (fun i _ => hw' i)
  calc
    N 0 ≤ ∫⁻ x, V x ^ c * ∏ i, A i x ^ w i ∂cubeMeasure μ (j+2) := by
      simpa only [T,V,pow_succ, r, b, a, c, N, Fin.prod_univ_succ, A, w, Fin.cons_zero, Fin.cons_succ] using
        reverse_raw_product_mass μ j ⟨hq,hsumθ,hrel⟩ ⟨hp1,hθ₀,hθ⟩ hF hM hN hmarg
    _ ≤ _ := hld
    _ ≤ _ := by
      rw [Fin.prod_univ_succ (fun i => (∫⁻ x, A i x ∂cubeMeasure μ (j+2)) ^ w i)]
      simp only [A, w, Fin.cons_zero, Fin.cons_succ, hTmass]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow hVmass hc.le) _

private theorem moment_regular {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (hn : ¬ (f =ᵐ[μ] 0))
    (d : ℕ) {p : ℝ} (hp : 0 < p) (hfin : gowers μ d p f < ⊤) :
    let I := ∫⁻ x, autocorrelation μ d f x ^ p ∂cubeMeasure μ d
    I ≠ 0 ∧ I ≠ ⊤ := by
  intro I
  have hg : gowers μ d p f ≠ 0 := fun h => hn ((gowers_eq_zero_iff μ d hp hf).mp h)
  have he : 0 < (1/p)*(1/(2:ℝ)^d) := by positivity
  unfold gowers lp at hfin hg
  rw [← ENNReal.rpow_mul] at hg
  have hI : I ≠ 0 := fun ez => hg ((ENNReal.rpow_eq_zero_iff_of_pos he).mpr ez)
  rw [← ENNReal.rpow_mul, ENNReal.rpow_lt_top_iff_of_pos he] at hfin
  exact ⟨hI,hfin.ne⟩

/-- The full reverse inequality in Theorem 1.4(a), with its finite-norm hypotheses. -/
theorem degree_reverse {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {k : ℕ} (hk : 1 ≤ k) {p : ℝ} {q θ : Fin (k+1) → ℝ}
    (h : DegreeParameters k p q θ) (hr : DegreeReverse p θ) {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) (hn : ¬ (f =ᵐ[μ] 0))
    (hU : gowers μ (k+1) p f < ⊤) (hl : ∀ i, gowers μ k (q i) f < ⊤) :
    lowerProduct μ k q θ f ≤ gowers μ (k+1) p f := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let N := fun i => ∫⁻ y, autocorrelation μ (j+1) f y ^ (q i) ∂cubeMeasure μ (j+1)
  let U := ∫⁻ x, autocorrelation μ (j+2) f x ^ p ∂cubeMeasure μ (j+2)
  have hp := zero_lt_one.trans hr.1
  have hu : U ≠ 0 ∧ U ≠ ⊤ := moment_regular μ hf hn (j+2) hp hU
  have hn' (i) : N i ≠ 0 ∧ N i ≠ ⊤ := moment_regular μ hf hn (j+1) (h.1 i) (hl i)
  have H := reverse_holder_marginals μ j h hr
    (measurable_autocorrelation_of_aemeasurable μ (j+2) hf)
    (measurable_autocorrelation_of_aemeasurable μ (j+1) hf) (fun i => (hn' i).2)
    (autocorrelation_marginal μ hf (j+1))
  let a := 1/(θ 0*p)
  let c := (p-1)/(θ 0*p)
  let b := fun t : Fin (j+1) => -(θ t.succ)/(θ 0)
  let r := 1/((j:ℝ)+1)
  change N 0 ≤ (∏ i, N i ^ r) ^ c * (U^a * ∏ t : Fin (j+1), N t.succ ^ b t) at H
  have hc : 0 ≤ c := (div_pos (sub_pos.mpr hr.1) (mul_pos hr.2.1 hp)).le
  have hnt (s : Fin (j+2) → ℝ) (i) : N i ^ s i ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (hn' i).1 (hn' i).2
  have hfin : ((∏ i, N i ^ r) ^ c * (U^a * ∏ t : Fin (j+1), N t.succ ^ b t)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hc (ENNReal.prod_ne_top (fun i _ => hnt (fun _ => r) i)))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hu.1 hu.2)
        (ENNReal.prod_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hn' i.succ).1 (hn' i.succ).2)))
  have HH := ENNReal.toReal_mono hfin H
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_prod] at HH
  have hsc := reverse_scalar hk h hr (fun i => ENNReal.toReal_pos (hn' i).1 (hn' i).2)
    (ENNReal.toReal_pos hu.1 hu.2) (by simpa [a,b,c,r,mul_left_comm,mul_assoc,mul_comm] using HH)
  have hmass : (∏ i, N i ^ (2*p*θ i/q i)) ≤ U := by
    apply (ENNReal.toReal_le_toReal (ENNReal.prod_ne_top (s := Finset.univ) (fun i _ => hnt (fun v => 2*p*θ v/q v) i)) hu.2).mp
    simpa only [ENNReal.toReal_prod, ← ENNReal.toReal_rpow] using hsc
  let t := (1/p)*(1/(2:ℝ)^(j+2))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have bound := ENNReal.rpow_le_rpow hmass ht
  rw [← ENNReal.prod_rpow_of_nonneg ht] at bound
  have hright : gowers μ (j+2) p f = U ^ t := by simp only [gowers,lp,U,t,← ENNReal.rpow_mul]
  rw [hright]
  apply le_trans ?_ bound
  apply le_of_eq
  unfold lowerProduct
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [gowers,lp,N,t]
  simp only [← ENNReal.rpow_mul]
  congr 1
  rw [pow_succ (2 : ℝ) (j+1)]
  field_simp [hp.ne',(h.1 i).ne']

/-- Theorem 1.4(a) of the introduction, in both parameter regimes. -/
theorem degree_inequalities : DegreeInequalities.{u} := by
  intro k hk p q θ h G _ _ _ _ _ _ _ _ μ _ f hf
  exact ⟨fun hp => degree_forward μ hk h hp hf,
    fun hr hn hU hl => degree_reverse μ hk h hr hf hn hU hl⟩

end LpGowers
