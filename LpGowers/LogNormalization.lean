module

public import LpGowers.BasicLogConvexity
public import LpGowers.Nonvanishing
public import LpGowers.Scaling
public import LpGowers.SubgroupObstruction

/-! Simultaneous normalization at the start of the proof of Theorem 1.1,
the two unit adjacent norms in §6. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace LpGowers

private theorem two_scale_factors (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b)
    (α β : ℝ) (hab : α ≠ β) :
    ∃ r s : ℝ≥0, 0 < r ∧ 0 < s ∧ s * (r ^ α * a) = 1 ∧ s * (r ^ β * b) = 1 := by
  let r : ℝ≥0 := (b/a) ^ (1 / (α-β))
  have hr : 0 < r := NNReal.rpow_pos (div_pos hb ha)
  have hq : r ^ (α-β) = b / a := by
    dsimp [r]
    rw [← NNReal.rpow_mul, one_div_mul_cancel (sub_ne_zero.mpr hab), NNReal.rpow_one]
  rw [NNReal.rpow_sub hr.ne'] at hq
  have he := (div_eq_div_iff (NNReal.rpow_pos (p := β) hr).ne' ha.ne').mp hq
  let v := r ^ α * a
  have hv : 0 < v := mul_pos (NNReal.rpow_pos hr) ha
  refine ⟨r, v⁻¹, hr, inv_pos.mpr hv, inv_mul_cancel₀ hv.ne', ?_⟩
  rw [mul_comm (r ^ β) b, ← he]
  exact inv_mul_cancel₀ hv.ne'

/-- Any input whose two adjacent ordinary Gowers norms are positive and
finite can be normalized to have both equal to one. The two positive
parameters multiply the Haar measure and input amplitude, respectively. -/
theorem normalize_adjacent_gowers {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) [SigmaFinite μ] (f : G → ℝ≥0) {d : ℕ} (hd : 2 ≤ d)
    (h0 : 0 < ordinaryGowers μ (d - 1) f) (hfin : ordinaryGowers μ (d - 1) f < ⊤)
    (h0' : 0 < ordinaryGowers μ (d + 1) f) (hfin' : ordinaryGowers μ (d + 1) f < ⊤) :
    ∃ r s : ℝ≥0, 0 < r ∧ 0 < s ∧
      ordinaryGowers (r • μ) (d - 1) (fun x => s * f x) = 1 ∧
      ordinaryGowers (r • μ) (d + 1) (fun x => s * f x) = 1 := by
  let e := fun n : ℕ => ((n : ℝ) + 1) / (2 : ℝ)^n
  have hne : e (d-1) ≠ e (d+1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
    dsimp only [e]
    rw [show 2+k-1 = k+1 by omega, show 2+k+1 = k+3 by omega]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
    intro h
    field_simp at h
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  let U := fun n : ℕ => (ordinaryGowers μ n f).toNNReal
  obtain ⟨r,s,hr,hs,hleft,hright⟩ := two_scale_factors (U (d-1)) (U (d+1))
    (ENNReal.toNNReal_pos h0.ne' hfin.ne) (ENNReal.toNNReal_pos h0'.ne' hfin'.ne) _ _ hne
  have applyScale (n : ℕ) (hn : ordinaryGowers μ n f < ⊤) (he : s * (r ^ e n * U n) = 1) :
      ordinaryGowers (r • μ) n (fun x => s * f x) = 1 := by
    have eq := congrArg (fun v : ℝ≥0 => (v : ℝ≥0∞)) he
    simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hr.ne', U,
      ENNReal.coe_toNNReal hn.ne, ENNReal.coe_one] at eq
    unfold ordinaryGowers
    rw [gowers_smul_input _ _ _ _ (by norm_num), gowers_smul_measure _ _ _ _ (by norm_num)]
    simpa [e, ordinaryGowers] using eq
  exact ⟨r,s,hr,hs,applyScale _ hfin hleft,applyScale _ hfin' hright⟩

/-- The uniform strict gap restricted to inputs with both adjacent norms one. -/
def NormalizedLogGap : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure],
      (¬ ∃ H : AddSubgroup G, IsCompact (H : Set G) ∧ IsOpen (H : Set G)) →
      ∀ (f : G → ℝ≥0), AEMeasurable f μ →
        ordinaryGowers μ (d - 1) f = 1 → ordinaryGowers μ (d + 1) f = 1 →
        ordinaryGowers μ d f ≤ ENNReal.ofReal (1 - ε)

/-- The normalized problem is equivalent to the full Theorem 1.1. This
also handles zero and infinite norms for an arbitrary measurable input. -/
theorem improvedLogConvexity_iff_normalized.{u} :
    ImprovedLogConvexity.{u} ↔ NormalizedLogGap.{u} := by
  constructor
  · intro H d hd
    obtain ⟨ε,hε,hε',gap⟩ := H d hd
    refine ⟨ε,hε,hε',?_⟩
    intro G _ _ _ _ _ _ _ _ μ _ hG f hf h₁ h₂
    simpa only [h₁,h₂,ENNReal.one_rpow,mul_one] using gap G μ hG f hf
  intro H d hd
  obtain ⟨ε,hε,hε',gap⟩ := H d hd
  refine ⟨ε,hε,hε',?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ hG f hf
  let c := ENNReal.ofReal (1-ε)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  let θ := logTheta d
  have hd' : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < 3 * (d : ℝ) - 2 := by linarith
  have hθ : 0 < θ := div_pos (by positivity) hden
  have hθ' : 0 < 1 - θ := sub_pos.mpr ((div_lt_one hden).mpr (by linarith))
  by_cases hz : f =ᵐ[μ] 0
  · rw [show ordinaryGowers μ d f = 0 from (gowers_eq_zero_iff μ d (by norm_num) hf).mpr hz]
    exact bot_le
  have hpos (n : ℕ) : 0 < ordinaryGowers μ n f :=
    pos_iff_ne_zero.mpr (fun h => hz ((gowers_eq_zero_iff μ n (by norm_num) hf).mp h))
  have hθa := (ENNReal.rpow_pos_of_nonneg (hpos (d-1)) hθ.le).ne'
  have hθb := (ENNReal.rpow_pos_of_nonneg (hpos (d+1)) hθ'.le).ne'
  change _ ≤ c * ordinaryGowers μ (d-1) f ^ θ * ordinaryGowers μ (d+1) f ^ (1-θ)
  by_cases h₁ : ordinaryGowers μ (d-1) f = ⊤
  · simp [h₁, ENNReal.top_rpow_of_pos hθ, hc, hθb]
  by_cases h₂ : ordinaryGowers μ (d+1) f = ⊤
  · simp [h₂, ENNReal.top_rpow_of_pos hθ', hc, hθa]
  obtain ⟨r,s,hr,hs,hn₁,hn₂⟩ := normalize_adjacent_gowers μ f hd
    (hpos _) (lt_top_iff_ne_top.mpr h₁) (hpos _) (lt_top_iff_ne_top.mpr h₂)
  let _ : (r • μ).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.coe_ne_zero.mpr hr.ne') ENNReal.coe_ne_top
  have hf' : AEMeasurable (fun x => s * f x) (r • μ) := (aemeasurable_const.mul hf).smul_measure r
  have hn := gap G (r • μ) hG (fun x => s * f x) hf' hn₁ hn₂
  let e := fun k : ℕ => ((k : ℝ) + 1) / (2 : ℝ)^k
  let k := fun n => (s : ℝ≥0∞) * (r : ℝ≥0∞) ^ e n
  have scale (n : ℕ) : ordinaryGowers (r • μ) n (fun x => s * f x) =
      k n * ordinaryGowers μ n f := by
    unfold ordinaryGowers
    rw [gowers_smul_input _ _ _ _ (by norm_num), gowers_smul_measure _ _ _ _ (by norm_num)]
    simp [k,e,mul_assoc]
  rw [scale] at hn hn₁ hn₂
  have balance : k (d-1)^θ * k (d+1)^(1-θ) = k d := by
    simp only [k, ENNReal.mul_rpow_of_nonneg _ _ hθ.le, ENNReal.mul_rpow_of_nonneg _ _ hθ'.le,
      ← ENNReal.rpow_mul]
    rw [mul_mul_mul_comm, ← ENNReal.rpow_add_of_nonneg _ _ hθ.le hθ'.le,
      show θ + (1-θ)=1 by ring, ENNReal.rpow_one,
      ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hr.ne') ENNReal.coe_ne_top]
    rw [← logTheta_balance d hd]
  have hunit : k d * (ordinaryGowers μ (d-1) f ^ θ * ordinaryGowers μ (d+1) f ^ (1-θ)) = 1 := by
    rw [← balance, mul_mul_mul_comm,
      ← ENNReal.mul_rpow_of_nonneg _ _ hθ.le, ← ENNReal.mul_rpow_of_nonneg _ _ hθ'.le,
      hn₁, hn₂, ENNReal.one_rpow, ENNReal.one_rpow, one_mul]
  have hkd : k d ≠ 0 := mul_ne_zero (ENNReal.coe_ne_zero.mpr hs.ne')
    (ENNReal.rpow_pos_of_nonneg (ENNReal.coe_pos.mpr hr) (show 0 ≤ e d by dsimp [e]; positivity)).ne'
  have hktf : k d ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by dsimp [e]; positivity) ENNReal.coe_ne_top)
  apply (ENNReal.mul_le_mul_iff_right hkd hktf).mp
  calc
    _ ≤ c := hn
    _ = c * (k d * (ordinaryGowers μ (d-1) f ^ θ * ordinaryGowers μ (d+1) f ^ (1-θ))) := by rw [hunit,mul_one]
    _ = _ := by ac_rfl

end LpGowers
