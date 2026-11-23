module

public import LpGowers.ReverseDegree
public import LpGowers.MonotoneApproximation
public import LpGowers.LogConvexityProofs

/-! The second chain of inequalities in §6 of Kovač and Rogers. The
specialization of reverse degree lowering is first evaluated where all
quantities are finite, then extended by monotone truncation. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LpGowers

private theorem finiteTruncation_input_moment {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] (f : G → ℝ≥0) (n K : ℕ) (hK : K ≠ 0) :
    (∫⁻ x, (finiteTruncation μ f n x : ℝ≥0∞) ^ K ∂μ) < ⊤ := by
  classical
  let S := spanningSets μ n
  calc
    _ ≤ ∫⁻ x, S.indicator (fun _ => (n : ℝ≥0∞)^K) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ S
      · simp only [finiteTruncation, Set.indicator_of_mem hx, S]
        exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr (min_le_right _ _)) _
      · simp [finiteTruncation, S, hx, hK]
    _ < ⊤ := by
      rw [lintegral_indicator_const (measurableSet_spanningSets μ n)]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) (measure_spanningSets_lt_top μ n)

/-- All positive integral powers of a truncation are integrable. Successive
integration of one cube increment then gives finite Gowers functionals for
every degree and every real outer exponent at least one. -/
theorem gowers_finiteTruncation_lt_top {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (n d : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    gowers μ d p (finiteTruncation μ f n) < ⊤ := by
  let v := finiteTruncation μ f n
  have hv : AEMeasurable v μ := aemeasurable_finiteTruncation μ hf n
  let M (k : ℕ) := ∫⁻ x, (v x : ℝ≥0∞) ^ (2 ^ k : ℕ) ∂μ
  have hm (k : ℕ) : M k < ⊤ := finiteTruncation_input_moment μ f n _ (by positivity)
  induction d generalizing p with
  | zero =>
    have hI : (∫⁻ x, (v x : ℝ≥0∞) ∂μ) ≠ ⊤ := by simpa [M] using (hm 0).ne
    simp only [gowers, lp, autocorrelation, cubeProduct, lintegral_const, cubeMeasure,
      Measure.pi_empty_univ, mul_one, pow_zero, div_one, ENNReal.rpow_one]
    exact (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hI)).lt_top
  | succ d ih =>
    let R := autocorrelation μ (d+1) v
    let ν := cubeMeasure μ (d+1)
    have hOne : gowers μ (d+1) 1 v < ⊤ := (gowers_one_succ_eq_gowers_two μ hv d) ▸ ih (by norm_num : (1:ℝ) ≤ 2)
    have hmR : (∫⁻ x, R x ∂ν) ≠ ⊤ := by
      change ((∫⁻ x, R x ^ (1 : ℝ) ∂ν) ^ (1 / (1 : ℝ))) ^ (1 / (2:ℝ)^(d+1)) < ⊤ at hOne
      intro htop
      simp only [ENNReal.rpow_one, div_one, htop, ENNReal.top_rpow_of_pos (by positivity : 0 < 1 / (2:ℝ)^(d+1)), lt_self_iff_false] at hOne
    have hbd (x) : R x ≤ M (d+1) := autocorrelation_le_lintegral_pow μ _ hv x
    have hb : 0 ≤ p - 1 := sub_nonneg.mpr hp
    have hi : (∫⁻ x, R x ^ p ∂ν) < ⊤ := calc
      _ ≤ ∫⁻ x, R x * M (d+1) ^ (p-1) ∂ν := by
        apply lintegral_mono
        intro x
        calc
          _ = R x ^ (1:ℝ) * R x ^ (p-1) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hb, show 1+(p-1) = p by ring]
          _ ≤ _ := by rw [ENNReal.rpow_one]; exact mul_le_mul_right (ENNReal.rpow_le_rpow (hbd x) hb) _
      _ < ⊤ := by
        have he := ENNReal.rpow_ne_top_of_nonneg hb (hm (d+1)).ne
        rw [lintegral_mul_const' _ _ he]
        exact (ENNReal.mul_ne_top hmR he).lt_top
    exact (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hi.ne)).lt_top


private theorem secondChain_regular {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {k : ℕ} (hk : 1 ≤ k)
    (hfin : ∀ n p, 1 ≤ p → gowers μ n p f < ⊤) :
    gowers μ k (6*(k:ℝ)/(3*k-1)) f ≤
      ordinaryGowers μ k f ^ (1/3:ℝ) * ordinaryGowers μ (k+2) f ^ (2/3:ℝ) := by
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) := by linarith
  let Q := 6*(k:ℝ)/(3*k-1)
  have hden : 0 < 3*(k:ℝ)-1 := by linarith
  have hQ : 1 ≤ Q := (one_le_div hden).mpr (by linarith)
  let q : Fin (k+1) → ℝ := Fin.cons Q (fun _ => 1)
  let θ : Fin (k+1) → ℝ := Fin.cons (3/2) (fun _ => -1/(2*(k:ℝ)))
  have hpar : DegreeParameters k 2 q θ := by
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · refine Fin.cases (zero_lt_one.trans_le hQ) (fun _ => by norm_num [q]) i
    · rw [Fin.sum_univ_succ]
      simp only [θ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · refine Fin.cases ?_ (fun t => ?_) i
      · simp only [q, θ, Fin.cons_zero, Q, Nat.cast_ofNat]
        field_simp
        ring
      · simp only [q, θ, Fin.cons_succ, Nat.cast_ofNat, div_one]
        ring
  have hrev : DegreeReverse 2 θ := ⟨by norm_num, by change (0:ℝ)<3/2; norm_num,
    fun _ => by simp only [θ, Fin.cons_succ]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)⟩
  by_cases hz : f =ᵐ[μ] 0
  · rw [(gowers_eq_zero_iff μ k (zero_lt_one.trans_le hQ) hf).mpr hz]
    exact bot_le
  have hqfin i : gowers μ k (q i) f < ⊤ := by
    apply hfin
    exact Fin.cases hQ (fun _ => le_rfl) i
  have h := degree_reverse μ hk hpar hrev hf hz (hfin _ _ (by norm_num)) hqfin
  let A := gowers μ k Q f
  let B := ordinaryGowers μ k f
  let C := ordinaryGowers μ (k+2) f
  have hB : B ≠ 0 := fun h => hz ((gowers_eq_zero_iff μ k (by norm_num) hf).mp h)
  have hB' : B ≠ ⊤ := (hfin k 1 le_rfl).ne
  have hC : C = gowers μ (k+1) 2 f := gowers_one_succ_eq_gowers_two μ hf _
  have hw : (-1 / (2*(k:ℝ))) * k = -(1/2:ℝ) := by field_simp
  have hc : A ^ (3/2:ℝ) * B ^ (-(1/2:ℝ)) ≤ C := by
    rw [hC]
    unfold lowerProduct at h
    rw [Fin.prod_univ_succ] at h
    simpa only [q, θ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hw, A, B, ordinaryGowers] using h
  have hx : A ^ (3/2:ℝ) ≤ C * B ^ (1/2:ℝ) := by
    simpa only [mul_assoc, ← ENNReal.rpow_add _ _ hB hB', neg_add_cancel, ENNReal.rpow_zero,
      mul_one] using (mul_le_mul_left hc (B ^ (1/2:ℝ)))
  have hpow := ENNReal.rpow_le_rpow hx (by norm_num : 0 ≤ (2/3:ℝ))
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3)] at hpow
  change A ≤ B ^ (1/3:ℝ) * C ^ (2/3:ℝ)
  simpa only [← ENNReal.rpow_mul, show (3/2:ℝ)*(2/3)=1 by norm_num, ENNReal.rpow_one,
    show (1/2:ℝ)*(2/3)=1/3 by norm_num, mul_comm] using hpow

/-- Section 6 bounds the upper outer exponent in the second interpolation
by the two ordinary adjacent norms. Positive-exponent monotone convergence
removes the auxiliary regularity assumptions in reverse degree lowering. -/
theorem logConvexity_second_endpoint {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    gowers μ (d-1) (6*((d:ℝ)-1)/(3*d-4)) f ≤
      ordinaryGowers μ (d-1) f ^ (1/3:ℝ) * ordinaryGowers μ (d+1) f ^ (2/3:ℝ) := by
  let k := d-1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have he : (k:ℝ) = (d:ℝ)-1 := by dsimp [k]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hpow : 6*((d:ℝ)-1)/(3*d-4) = 6*(k:ℝ)/(3*k-1) := by rw [he]; ring_nf
  have hn : k+2=d+1 := by dsimp [k]; omega
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < 6*(k:ℝ)/(3*k-1) := div_pos (by linarith) (by linarith)
  rw [hpow, gowers_eq_iSup_finiteTruncation μ hf _ hp]
  apply iSup_le
  intro n
  have hv := aemeasurable_finiteTruncation μ hf n
  have H := secondChain_regular μ hv hk (fun m p hp => gowers_finiteTruncation_lt_top μ hf n m hp)
  rw [hn] at H
  have hs : finiteTruncation μ f n ≤ f := by
    intro x
    by_cases hx : x ∈ spanningSets μ n <;> simp [finiteTruncation,hx]
  exact H.trans (mul_le_mul' (ENNReal.rpow_le_rpow (gowers_mono μ hs _ (by norm_num : (0:ℝ)<1)) (by norm_num))
    (ENNReal.rpow_le_rpow (gowers_mono μ hs _ (by norm_num : (0:ℝ)<1)) (by norm_num)))

end LpGowers
