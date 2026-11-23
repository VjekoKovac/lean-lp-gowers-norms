module

public import LpGowers.LogMoments

/-! The three lower-degree autocorrelation moments in §6 under the
normalization of the adjacent ordinary Gowers functionals. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

/-- The second interpolation chain gives the three moments at degree
`d-1` simultaneously. The moment of exponent one equals one exactly. -/
theorem normalized_lower_moments.{u} (j : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ (G : Type u) [AddCommGroup G] [MeasurableSpace G]
      [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ] (f : G → ℝ≥0),
      AEMeasurable f μ → ordinaryGowers μ (j+1) f = 1 → ordinaryGowers μ (j+2+1) f = 1 →
      ENNReal.ofReal (1-δ) ≤ ordinaryGowers μ (j+2) f →
      let c := 6*(((j+2:ℕ):ℝ)-1)/(3*((j+2:ℕ):ℝ)-4)
      ∀ t ∈ ({1,2,c}:Set ℝ),
        ENNReal.ofReal (1-η) ≤ ∫⁻ x, (autocorrelation μ (j+1) f x)^t ∂cubeMeasure μ (j+1) ∧
        (∫⁻ x, (autocorrelation μ (j+1) f x)^t ∂cubeMeasure μ (j+1)) ≤ 1 := by
  let D := j+2
  have hD : 2 ≤ D := by dsimp [D]; omega
  have hDr : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hdiff : D-1 = j+1 := by simp [D]
  let c := 6*((D:ℝ)-1)/(3*D-4)
  let w := 1-1/(3*(D:ℝ)-2)
  let P := (2:ℝ)^(j+1)
  have hc : 0<c := div_pos (by linarith) (by linarith)
  have hw : 0<w := sub_pos.mpr ((div_lt_one (by linarith : 0<3*(D:ℝ)-2)).mpr (by linarith))
  have hP : 0<P := by dsimp [P]; positivity
  let Q := 2*P + P*c/w
  have hwP : 0<P*c/w := by positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  obtain ⟨δ,hδ,hδ',H⟩ := near_one_powers hη hQ
  refine ⟨δ,hδ,hδ',?_⟩
  intro G _ _ _ μ _ _ f hf hlow hhigh hmid
  change ordinaryGowers μ (D+1) f = 1 at hhigh
  dsimp only
  let U := ordinaryGowers μ D f
  let A := gowers μ (j+1) c f
  have hA : A ≤ 1 := by
    have h := logConvexity_second_endpoint μ hf hD
    simpa only [hdiff,hlow,hhigh,ENNReal.one_rpow,mul_one] using h
  have hU : U ≤ A^w := by
    have h := logConvexity_second_interpolation μ hf hD
    simpa only [hdiff, hlow, ENNReal.one_rpow, one_mul] using h
  have hu1 : U ≤ 1 := hU.trans (ENNReal.rpow_le_one hA hw.le)
  have hU' : U ^ (1/w) ≤ A := by
    simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hw.ne', ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow hU (one_div_nonneg.mpr hw.le)
  have hcU := ENNReal.rpow_le_rpow hU' (mul_nonneg hP.le hc.le)
  rw [← ENNReal.rpow_mul, show 1/w*(P*c)=P*c/w by ring] at hcU
  have hU2 : U = gowers μ (j+1) 2 f := gowers_one_succ_eq_gowers_two μ hf (j+1)
  intro t ht
  rcases ht with rfl | rfl | ht
  · rw [← gowers_moment_power μ _ (show (0:ℝ)<1 by norm_num) f,
      show gowers μ (j+1) 1 f = 1 from hlow, ENNReal.one_rpow]
    exact ⟨ENNReal.ofReal_le_one.mpr (by linarith), le_rfl⟩
  · rw [← gowers_moment_power μ _ (show (0:ℝ)<2 by norm_num) f, ← hU2]
    exact ⟨H U hu1 hmid (P*2) (by dsimp [Q]; linarith), ENNReal.rpow_le_one hu1 (by positivity)⟩
  · have htc : t=c := ht
    subst t
    rw [← gowers_moment_power μ _ hc f]
    exact ⟨(H U hu1 hmid _ (by dsimp [Q]; linarith)).trans hcU,
      ENNReal.rpow_le_one hA (mul_nonneg hP.le hc.le)⟩

end LpGowers
