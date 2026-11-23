module

public import LpGowers.DegreeNear

/-! # Proximity of the normalized joint density to its Loomis–Whitney product

The proof retains the individual marginal exponents in the forward direction
of Section 5. -/

public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

private theorem weighted_factor {ι : Type*} [Fintype ι] (p r b : ℝ) (q a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : 0 ≤ b) (hsum : (∑ i, a i) = p)
    (hcancel : ∀ i, q i*r*b + (q i-2)*a i = 0)
    (z : ℝ≥0∞) (m N : ι → ℝ≥0∞) (hm : ∀ i,m i ≠ 0 ∧ m i ≠ ⊤)
    (hN : ∀ i,N i ≠ 0 ∧ N i ≠ ⊤) (hr : 0 ≤ r) :
    (∏ i, (m i ^ (q i) * (N i)⁻¹)^r)^b * ∏ i, (z * m i^(q i-2) * (N i)⁻¹)^a i =
    z^p * ∏ i, (N i) ^ (-(r*b+a i)) := by
  rw [← ENNReal.prod_rpow_of_nonneg hb]
  simp only [← ENNReal.rpow_mul,ENNReal.mul_rpow_of_nonneg _ _ (mul_nonneg hr hb),
    ENNReal.mul_rpow_of_nonneg _ _ (ha _), ← ENNReal.rpow_mul, ENNReal.inv_rpow,
    ← ENNReal.rpow_neg]
  rw [← Finset.prod_mul_distrib]
  have each (i : ι) : (m i ^ (q i*(r*b)) * N i ^ (-(r*b))) *
      (z ^ a i * m i ^ ((q i-2)*a i) * N i ^ (-a i)) = z ^ a i * N i ^ (-(r*b+a i)) := by
    calc
      _ = z ^ a i * (m i ^ (q i*(r*b)) * m i ^ ((q i-2)*a i)) * (N i^(-(r*b))*N i^(-a i)) := by ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ (hm i).1 (hm i).2,show q i * (r*b)+(q i-2)*a i = 0 by simpa only [mul_assoc] using hcancel i,
          ENNReal.rpow_zero,mul_one,← ENNReal.rpow_add _ _ (hN i).1 (hN i).2,neg_add_rev,add_comm (-a i)]
  simp only [each,Finset.prod_mul_distrib,prod_const_rpow_of_nonneg z _ a ha,hsum]

/-- In the forward non-endpoint regime near equality makes the normalized
joint moment close to the Loomis–Whitney product of its normalized faces. -/
theorem degree_forward_near (j : ℕ) {p : ℝ} {q θ : Fin (j+2) → ℝ}
    (hpar : DegreeParameters (j+1) p q θ) (hfor : DegreeForward p θ) (hp_ne : p ≠ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ (G : Type u) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
      (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ] (f : G → ℝ≥0),
      AEMeasurable f μ → (0 < gowers μ (j+2) p f ∧ gowers μ (j+2) p f < ⊤) →
      (∀ i, 0 < gowers μ (j+1) (q i) f ∧ gowers μ (j+1) (q i) f < ⊤) →
      ENNReal.ofReal (1-ε) * lowerProduct μ (j+1) q θ f ≤ gowers μ (j+2) p f →
      jointFaceError μ j p q f ≤ ENNReal.ofReal η := by
  let a := fun i => θ i * p
  let b := 1-p
  let r := 1/((j:ℝ)+1)
  have ha i : 0 < a i := mul_pos (hfor.2.2 i) hfor.1
  have hb : 0 < b := sub_pos.mpr (lt_of_le_of_ne hfor.2.1 hp_ne)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : ∑ i, a i = p := by simp only [a,← Finset.sum_mul,hpar.2.1,one_mul]
  let γ : Fin (j+3) → ℝ := Fin.cons b a
  have hγ (i) : 0 < γ i := Fin.cases hb ha i
  have hγs : (∑ i, γ i) = 1 := by rw [Fin.sum_univ_succ]; simp only [γ,Fin.cons_zero,Fin.cons_succ,hsum,b]; ring
  let t := (2:ℝ)^(j+2)*p
  have ht : 0 < t := mul_pos (by positivity) hfor.1
  obtain ⟨σ,hσ,Hholder⟩ := holder_stability_ennreal (ι := Fin (j+3)) γ hγ hγs (by linarith : 0 < η/2)
  let τ := min (σ/2) (η/2)
  have hτ : 0 < τ := lt_min (by linarith) (by linarith)
  obtain ⟨δ,hδ,_,hpower⟩ := small_power_deficit t hτ
  refine ⟨δ,hδ,?_⟩
  intro ε he hε G _ _ _ μ _ _ f hf hhigh hlow hnear
  let ν := cubeMeasure μ (j+2)
  let ν' := cubeMeasure μ (j+1)
  let F := autocorrelation μ (j+2) f
  let M := autocorrelation μ (j+1) f
  let U := ∫⁻ x, (F x)^p ∂ν
  let N := fun i => ∫⁻ x, (M x)^(q i) ∂ν'
  let z := fun i => 2*p*θ i/q i
  let K := ∏ i, (N i) ^ z i
  let D := U/K
  let W := momentDensity ν p F
  let V := lwProduct j (fun i => momentDensity ν' (q i) M)
  let T := fun (i : Fin (j+2)) x => (F x * M (deleteCoord i x) ^ (q i-2)) / N i
  let H : Fin (j+3) → (Fin (j+2) → G) → ℝ≥0∞ := Fin.cons V T
  let P := fun x => ∏ i, (H i x)^(γ i)
  have hm : Measurable M := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hF : Measurable F := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hU : U ≠ 0 ∧ U ≠ ⊤ := moment_regular_of_gowers μ _ hfor.1 hhigh
  have hN i : N i ≠ 0 ∧ N i ≠ ⊤ := moment_regular_of_gowers μ _ (hpar.1 i) (hlow i)
  have hz i : 0 < z i := div_pos (mul_pos (mul_pos (by norm_num) hfor.1) (hfor.2.2 i)) (hpar.1 i)
  have hK0 : K ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ e => (hN i).1 ((ENNReal.rpow_eq_zero_iff_of_pos (hz i)).mp e))
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun i _ => ENNReal.rpow_ne_top_of_ne_zero (hN i).1 (hN i).2)
  have hw : Measurable W := momentDensity_measurable ν p hF
  have hv : Measurable V := lwProduct_measurable (fun i => momentDensity_measurable ν' (q i) hm)
  have hw1 : (∫⁻ x, W x ∂ν) = 1 := momentDensity_integral ν p hF hU.1 hU.2
  have hT i : Measurable (T i) := (hF.mul ((hm.comp (measurable_omitCoord i)).pow_const _)).div_const _
  have hH i : Measurable (H i) := Fin.cases hv hT i
  have hHm (i) : (∫⁻ x,H i x ∂ν) ≤ 1 := by
    cases i using Fin.cases with
    | zero =>
      have hh := functionalLoomisWhitney μ j (fun i => momentDensity ν' (q i) M)
        (fun i => momentDensity_measurable ν' (q i) hm)
      change (∫⁻ x, V x ∂ν) ≤ 1
      apply hh.trans
      apply Finset.prod_le_one
      intro i _
      have hmass := momentDensity_integral ν' (q i) hm (hN i).1 (hN i).2
      change (∫⁻ y, momentDensity ν' (q i) M y ∂ν') ^ r ≤ 1
      rw [hmass,ENNReal.one_rpow]
    | succ i =>
      change (∫⁻ x,T i x ∂ν) ≤ 1
      simp only [T,div_eq_mul_inv]
      rw [lintegral_mul_const (f := fun x => F x * M (deleteCoord i x) ^ (q i-2)) _
        (hF.mul ((hm.comp (measurable_omitCoord i)).pow_const _)),
        tilted_marginal_integral μ i hF hm (hpar.1 i) (hN i).2 (autocorrelation_marginal μ hf (j+1) i)]
      exact (ENNReal.mul_inv_cancel (hN i).1 (hN i).2).le
  have hc (i) : q i*r*b + (q i-2)*a i = 0 := by
    have h := hpar.2.2 i
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h
    dsimp [r,b,a]
    have hj : 0 < (j:ℝ)+1 := by positivity
    field_simp [hj.ne',hfor.1.ne',(hpar.1 i).ne'] at h ⊢
    nlinarith only [h]
  have hcoef (i) : r*b+a i = z i := by
    dsimp [z]
    apply (eq_div_iff (hpar.1 i).ne').2
    have H := hc i
    dsimp only [a] at H ⊢
    nlinarith only [H]
  have hvalid := ae_all_iff.mpr (fun i => finite_marginal_on_support μ i hF hm (hpar.1 i) (hN i).2
    (autocorrelation_marginal μ hf (j+1) i))
  have hPeq : P =ᵐ[ν] fun x => D*W x := by
    filter_upwards [hvalid] with x hx
    dsimp only [P]
    rw [Fin.prod_univ_succ]
    simp only [H,γ,Fin.cons_zero,Fin.cons_succ]
    by_cases h0 : F x = 0
    · have hz0 : (∏ i, T i x ^ a i) = 0 := Finset.prod_eq_zero (Finset.mem_univ 0)
          (by simp [T,h0,ENNReal.zero_rpow_of_pos (ha 0)])
      simp [hz0,W,momentDensity,h0,ENNReal.zero_rpow_of_pos hfor.1]
    · have en := weighted_factor p r b q a (fun i => (ha i).le) hb.le hsum hc (F x)
        (fun i => M (deleteCoord i x)) N (fun i => hx i h0) hN hr
      change (∏ i, ((M (deleteCoord i x))^(q i) / N i)^r)^b *
         (∏ i, (F x * (M (deleteCoord i x))^(q i-2) / N i)^(a i)) = D*W x
      simp only [div_eq_mul_inv]
      rw [en]
      simp only [hcoef,ENNReal.rpow_neg]
      rw [← ENNReal.prod_inv_distrib (fun i _ _ _ _ => Or.inl
        (fun h => (hN i).1 ((ENNReal.rpow_eq_zero_iff_of_pos (hz i)).mp h)))]
      change F x ^ p * K⁻¹ = (U*K⁻¹)*(F x ^ p * U⁻¹)
      calc
        _ = (U*U⁻¹)*(F x^p*K⁻¹) := by rw [ENNReal.mul_inv_cancel hU.1 hU.2,one_mul]
        _ = _ := by ac_rfl
  have hPmass : (∫⁻ x,P x ∂ν) = D := by rw [lintegral_congr_ae hPeq,lintegral_const_mul D hw,hw1,mul_one]
  have hconv := degree_moment_conversion μ (j+1) hfor.1 q θ hpar.1 f
  have Dle : D ≤ 1 := by
    have h' := ENNReal.rpow_le_rpow (degree_forward μ (by omega : 1 ≤ j+1) hpar hfor hf) ht.le
    rw [hconv.1,hconv.2] at h'
    exact (mul_le_mul_left h' K⁻¹).trans_eq (ENNReal.mul_inv_cancel hK0 hKt)
  have hnear' := ENNReal.rpow_le_rpow hnear ht.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, hconv.1,hconv.2] at hnear'
  have hlowD : ENNReal.ofReal (1-τ) ≤ D := by
    apply (hpower ε he.le hε).trans
    apply le_trans ?_ (mul_le_mul_left hnear' K⁻¹)
    change _ ≤ _ * K * K⁻¹
    rw [mul_assoc,ENNReal.mul_inv_cancel hK0 hKt,mul_one]
  have hPnear : ENNReal.ofReal (1-τ) ≤ ∫⁻ x,P x ∂ν := hPmass.symm ▸ hlowD
  have hτs : τ < σ := (min_le_left _ _).trans_lt (by linarith)
  have hh := (Hholder τ hτ.le hτs ν H (fun i => (hH i).aemeasurable) hHm hPnear 0).1
  change l1DensityError ν V P ≤ ENNReal.ofReal (η/2) at hh
  rw [l1DensityError_congr_ae ν (Filter.EventuallyEq.rfl) hPeq] at hh
  have hdlo : 1-D ≤ ENNReal.ofReal τ := by
    apply tsub_le_iff_tsub_le.mp
    simpa [ENNReal.ofReal_sub _ hτ.le] using hlowD
  change l1DensityError ν W V ≤ ENNReal.ofReal η
  rw [l1DensityError_comm ν W V]
  apply (l1DensityError_triangle ν (F := V) (G := fun x => D*W x) (H := W)
    hv (measurable_const.mul hw) hw).trans
  rw [l1DensityError_small_scaling ν hw hw1 Dle]
  have he' := add_le_add hh hdlo
  apply he'.trans
  rw [← ENNReal.ofReal_add (by linarith) hτ.le]
  apply ENNReal.ofReal_le_ofReal
  have hτη : τ ≤ η/2 := min_le_right _ _
  linarith only [hτη]

end LpGowers
