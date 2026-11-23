module

public import LpGowers.BasicLogConvexity
public import LpGowers.DegreeStability
public import LpGowers.SecondLogChain

/-! # The moment deficits in the normalized chains of Section 6

Writing the degree as `j+2` keeps the codimension-one faces nonempty.
All deficit tolerances are uniform over the ambient Haar measure and input.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

def logLowerPower (d : ℕ) : ℝ := (d : ℝ) / (2*d-1)

theorem logLower_parameters (j : ℕ) :
    DegreeParameters (j+1) (logLowerPower (j+2)) (fun _ => 1) (fun _ => 1/((j:ℝ)+2)) ∧
    DegreeForward (k:=j+1) (logLowerPower (j+2)) (fun _ => 1/((j:ℝ)+2)) ∧
    logLowerPower (j+2)<1 := by
  have hden : 0 < 2*((j:ℝ)+2)-1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hstrict : logLowerPower (j+2)<1 := by
    unfold logLowerPower
    push_cast
    exact (div_lt_one hden).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  refine ⟨⟨fun _ => one_pos,?_,?_⟩,⟨?_,hstrict.le,fun _ => by positivity⟩,hstrict⟩
  · simp; field_simp; ring
  · intro i
    unfold logLowerPower
    push_cast
    field_simp
    ring
  · unfold logLowerPower
    push_cast
    exact div_pos (by positivity) hden

theorem gowers_moment_power {G : Type*} [MeasurableSpace G] [AddCommMonoid G] (μ : Measure G)
    (d : ℕ) {p : ℝ} (hp : 0<p) (f : G → ℝ≥0) :
    gowers μ d p f ^ ((2:ℝ)^d*p) = ∫⁻ x, (autocorrelation μ d f x)^p ∂cubeMeasure μ d := by
  simp only [gowers,lp,← ENNReal.rpow_mul]
  have he : (1/p)*(1/(2:ℝ)^d)*((2:ℝ)^d*p)=1 := by field_simp
  rw [he,ENNReal.rpow_one]

/-- Powers up to a fixed exponent remain uniformly near one. -/
theorem near_one_powers {η Q : ℝ} (hη : 0<η) (hQ : 0<Q) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ u : ℝ≥0∞, u ≤ 1 → ENNReal.ofReal (1-δ) ≤ u →
      ∀ q : ℝ, q ≤ Q → ENNReal.ofReal (1-η) ≤ u^q := by
  let β := min η (1/2)
  have hβ : 0<β := lt_min hη (by norm_num)
  have hβ1 : β<1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  let δ := 1-(1-β)^(1/Q)
  have hbase := sub_pos.mpr hβ1
  have hδ : 0<δ := sub_pos.mpr (Real.rpow_lt_one hbase.le (by linarith) (one_div_pos.mpr hQ))
  have hδ1 : δ<1 := sub_lt_self _ (Real.rpow_pos_of_pos hbase _)
  refine ⟨δ,hδ,hδ1,?_⟩
  intro u hu hn q hq
  refine (ENNReal.ofReal_le_ofReal (sub_le_sub_left (min_le_left η (1/2)) 1)).trans
    ((le_trans ?_ (ENNReal.rpow_le_rpow hn hQ.le)).trans (ENNReal.rpow_le_rpow_of_exponent_ge hu hq))
  rw [ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hδ1.le) hQ.le]
  dsimp [δ]
  rw [sub_sub_cancel,← Real.rpow_mul hbase.le,one_div_mul_cancel hQ.ne',Real.rpow_one]

/-- Uniform control of the three upper-degree integrals and the symmetric
degree-lowering near-equality hypothesis by the original ordinary deficit. -/
theorem normalized_upper_moments.{u} (j : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G]
      [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0),
      AEMeasurable f μ → ordinaryGowers μ (j+1) f = 1 → ordinaryGowers μ (j+2+1) f = 1 →
      ENNReal.ofReal (1-δ) ≤ ordinaryGowers μ (j+2) f →
      (ENNReal.ofReal (1-η) ≤ gowers μ (j+2) (logLowerPower (j+2)) f ∧
        gowers μ (j+2) (logLowerPower (j+2)) f ≤ 1) ∧
      ∀ t ∈ ({logLowerPower (j+2),1,2}:Set ℝ),
        ENNReal.ofReal (1-η) ≤ ∫⁻ x, (autocorrelation μ (j+2) f x)^t ∂cubeMeasure μ (j+2) ∧
        (∫⁻ x, (autocorrelation μ (j+2) f x)^t ∂cubeMeasure μ (j+2)) ≤ 1 := by
  let D := j+2
  let a := logLowerPower D
  let θ := logTheta D
  let P : ℝ := 2^D
  have hD : 2≤D := by dsimp [D]; omega
  have hDr : (2:ℝ)≤D := by exact_mod_cast hD
  have hθ : 0<θ := div_pos (by linarith) (by linarith)
  have hP : 0<P := by dsimp [P]; positivity
  obtain ⟨hpar,hfor,ha1⟩ := logLower_parameters j
  have ha : 0<a := hfor.1
  let Q := 1/θ + P + P*a/θ
  have hQ : 0<Q := by dsimp [Q]; positivity
  obtain ⟨δ,hδ,hδ1,H⟩ := near_one_powers hη hQ
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf hlow hhigh hmid
  let U := ordinaryGowers μ D f
  let A := gowers μ D a f
  have hprod : lowerProduct μ (j+1) (fun _ => 1) (fun _ => 1/((j:ℝ)+2)) f = 1 := by
    change gowers μ (j+1) 1 f = 1 at hlow
    simp [lowerProduct,hlow]
  have hA : A≤1 := by
    rw [← hprod]
    exact (degree_inequalities (j+1) (by omega) a _ _ hpar G μ f hf).1 hfor
  have hUθ : U ≤ A^θ := by
    have h := logConvexity_first_interpolation μ hf hD
    rw [hhigh,ENNReal.one_rpow,mul_one] at h
    exact h
  have hU : U ≤ 1 := hUθ.trans (ENNReal.rpow_le_one hA hθ.le)
  have haU : U^(1/θ) ≤ A := by
    simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hθ.ne', ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow hUθ (one_div_nonneg.mpr hθ.le)
  have hUp := H U hU hmid
  have hPa : 0<P*a/θ := by positivity
  have haU' := ENNReal.rpow_le_rpow haU (mul_nonneg hP.le ha.le)
  rw [← ENNReal.rpow_mul,show 1/θ*(P*a)=P*a/θ by ring] at haU'
  have hiθ := one_div_pos.mpr hθ
  have hqa : P*a/θ≤Q := by dsimp [Q]; linarith
  have hqθ : 1/θ≤Q := by dsimp [Q]; linarith
  have hqP : P≤Q := by dsimp [Q]; linarith
  refine ⟨⟨(hUp _ hqθ).trans haU,hA⟩,?_⟩
  intro t ht
  rcases ht with rfl | rfl | ht
  · rw [← gowers_moment_power μ _ ha f]
    exact ⟨(hUp _ hqa).trans haU', ENNReal.rpow_le_one hA (mul_nonneg hP.le ha.le)⟩
  · rw [← gowers_moment_power μ _ (show (0:ℝ)<1 by norm_num) f,mul_one]
    exact ⟨hUp _ hqP, ENNReal.rpow_le_one hU hP.le⟩
  · have ht2 : t=2 := ht
    subst t
    have htwo := gowers_one_succ_eq_gowers_two μ hf (j+2)
    change ordinaryGowers μ (j+2+1) f = gowers μ (j+2) 2 f at htwo
    rw [hhigh] at htwo
    rw [← gowers_moment_power μ _ (show (0:ℝ)<2 by norm_num) f,← htwo,ENNReal.one_rpow]
    exact ⟨ENNReal.ofReal_le_one.mpr (by linarith),le_rfl⟩

end LpGowers
