module

public import LpGowers.YoungCorrelationOperator
public import LpGowers.YoungPowerMap
public import LpGowers.YoungUnitInput
public import LpGowers.YoungEuler
public import LpGowers.YoungUpdateMap
import Mathlib.Tactic

/-! The diagonal Young Euler map on the real critical Lebesgue space, written
as the composition of the two bounded correlations and the signed powers. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LpGowers

theorem young_outer_power_ge_one {s : ℝ} (hs : 1 < s) : 1 ≤ 2*s/(s-1)-1 := by
  have h : 2 ≤ 2*s/(s-1) := (le_div_iff₀ (sub_pos.mpr hs)).2 (by linarith)
  linarith

theorem young_inner_exponents {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal s = ENNReal.ofReal (s/(s-1))*ENNReal.ofReal (s-1) := by
  rw [← ENNReal.ofReal_mul (div_pos (zero_lt_one.trans hs) (sub_pos.mpr hs)).le,
    div_mul_cancel₀ _ (sub_pos.mpr hs).ne']

theorem young_outer_exponents {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (2*s/(s-1)) =
      ENNReal.ofReal (2*s/(s+1))*ENNReal.ofReal (2*s/(s-1)-1) := by
  rw [← ENNReal.ofReal_mul (by have := zero_lt_one.trans hs; positivity)]
  congr 1
  field_simp
  ring

section
variable (n : ℕ) (s : ℝ) (hs : 2 ≤ s)
variable [Fact (1≤ENNReal.ofReal (2*s/(s+1)))] [Fact (1≤ENNReal.ofReal s)]
  [Fact (1≤ENNReal.ofReal (s/(s-1)))] [Fact (1≤ENNReal.ofReal (2*s/(s-1)))]
local notation "μ" => euclideanMeasure n
local notation "q" => (2*s/(s+1))
local notation "v" => (2*s/(s-1))
local notation "r" => (s/(s-1))
include hs

/-- The signed real-Lᵖ realization of the normalized nonlinear Euler update. -/
def youngRealEuler : EuclideanLp n q → EuclideanLp n q :=
  youngUpdateMap (((youngMomentConstant 1 n s)⁻¹).toReal^(v-1))
    (diagonalCorrCLM n s (by linarith)) (adjointCorrCLM n s (by linarith))
    (signedPowerLp μ (ENNReal.ofReal s) (ENNReal.ofReal r) (s-1) (by linarith)
      (young_inner_exponents (by linarith)))
    (signedPowerLp μ (ENNReal.ofReal v) (ENNReal.ofReal q) (v-1)
      (young_outer_power_ge_one (by linarith)) (young_outer_exponents (by linarith)))

/-- The signed map, restricted to positive inputs, represents the explicit
nonnegative Euler integral almost everywhere. -/
theorem youngRealEuler_ae (f : EuclideanLp n q) (F : Rn n → ℝ≥0)
    (hf : (fun x => f x) =ᵐ[μ] fun x => (F x : ℝ)) :
    (fun x => youngRealEuler n s hs f x) =ᵐ[μ] fun x => (youngEuler n s F x : ℝ) := by
  have hs1 : 1 < s := by linarith
  have ht : 0 < s-1 := sub_pos.mpr hs1
  have hq0 : 0 < q := by positivity
  have hv0 : 0 < v := by positivity
  have hr0 : 0 < r := by positivity
  let A := diagonalCorrCLM n s hs1 f f
  let R := pairCorrelation μ (liftNN F) (liftNN F)
  let H := fun t => (R t)^(s-1)
  let P := signedPowerLp μ (ENNReal.ofReal s) (ENNReal.ofReal r) (s-1) (by linarith)
      (young_inner_exponents hs1) A
  let J := adjointCorrCLM n s hs1 P f
  let Q := signedPowerLp μ (ENNReal.ofReal v) (ENNReal.ofReal q) (v-1) (young_outer_power_ge_one hs1)
      (young_outer_exponents hs1) J
  let B := pairCorrelation μ H (liftNN F)
  let K := youngMomentConstant 1 n s
  let c := K⁻¹.toReal ^ (v-1)
  have hn : (0 : Rn n → ℝ) ≤ᵐ[μ] ⇑f := by filter_upwards [hf] with x hx; simp [hx]
  have he : (fun x => ENNReal.ofReal (f x)) =ᵐ[μ] liftNN F := by
    filter_upwards [hf] with x hx; simp [hx,liftNN]
  have hA := corrCLM_nonnegative_ae hq0 hq0 (zero_lt_one.trans hs1) ENNReal.one_ne_top
    (firstUpdateBound n s hs1) f f hn hn he he
  have hP : ∀ᵐ x ∂μ, H x ≠ ⊤ ∧ P x = (H x).toReal := by
    filter_upwards [hA,signedPowerLp_coe μ (ENNReal.ofReal s) (ENNReal.ofReal r) (s-1)
      (by linarith) (young_inner_exponents hs1) A] with x hx hy
    change R x ≠ ⊤ ∧ A x = (R x).toReal at hx
    refine ⟨ENNReal.rpow_ne_top_of_nonneg ht.le hx.1,?_⟩
    change signedPowerLp _ _ _ _ _ _ _ x = _
    rw [hy,hx.2,signedPower_nonneg_value (by linarith) ENNReal.toReal_nonneg]
    exact ENNReal.toReal_rpow _ _
  have hPn : (0 : Rn n → ℝ) ≤ᵐ[μ] ⇑P := by
    filter_upwards [hP] with x hx; rw [hx.2]; exact ENNReal.toReal_nonneg
  have hPe : (fun x => ENNReal.ofReal (P x)) =ᵐ[μ] H := by
    filter_upwards [hP] with x hx; rw [hx.2,ENNReal.ofReal_toReal hx.1]
  have hJ := corrCLM_nonnegative_ae hr0 hq0 hv0 ENNReal.one_ne_top (secondUpdateBound n s hs1)
    P f hPn hn hPe he
  have hscale (x) : sharpYoungScore n s F x = K⁻¹ * B x := by
    dsimp only [sharpYoungScore,K,B,pairCorrelation,H,R]
    simp_rw [add_comm x]
    rfl
  filter_upwards [hJ, signedPowerLp_coe μ (ENNReal.ofReal v) (ENNReal.ofReal q) (v-1)
    (young_outer_power_ge_one hs1) (young_outer_exponents hs1) J, Lp.coeFn_smul c Q] with x hx hy hz
  change B x ≠ ⊤ ∧ J x = (B x).toReal at hx
  change Q x = signedPower (v-1) (J x) at hy
  change (c • Q) x = c * Q x at hz
  change (c • Q) x = _
  rw [hz,hy,hx.2,signedPower_nonneg_value (young_outer_power_ge_one hs1) ENNReal.toReal_nonneg]
  simp only [youngEuler,NNReal.coe_rpow,hscale]
  change _ = (K⁻¹ * B x).toReal ^ (v-1)
  rw [ENNReal.toReal_mul,Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

/-- Every unit near-extremizing sequence is an approximate fixed-point sequence
of the concrete signed Young map in the critical real Lᵖ distance. -/
theorem tendsto_dist_youngRealEuler (f : ℕ → EuclideanLp n q) (F : ℕ → Rn n → ℝ≥0)
    (hF : ∀ k, AEMeasurable (F k) μ)
    (he : ∀ k, (fun x => f k x) =ᵐ[μ] fun x => (F k x : ℝ))
    (hm : ∀ k, (∫⁻ x, (F k x : ℝ≥0∞) ^ (criticalExponent 1 s) ∂μ) = 1)
    (hJ : Tendsto (fun k => cubeMoment 1 n s (F k)) atTop (𝓝 (youngMomentConstant 1 n s))) :
    Tendsto (fun k => dist (f k) (youngRealEuler n s hs (f k))) atTop (𝓝 0) := by
  let K := youngMomentConstant 1 n s
  let U := fun k => (hF k).mk (F k)
  have hU k : Measurable (U k) := (hF k).measurable_mk
  have hFU k : F k =ᵐ[μ] U k := (hF k).ae_eq_mk
  have hrep k : (fun x => f k x) =ᵐ[μ] fun x => (U k x : ℝ) :=
    (he k).trans ((hFU k).fun_comp (fun t : ℝ≥0 => (t : ℝ)))
  have hmass k : (∫⁻ x,(U k x : ℝ≥0∞)^criticalExponent 1 s ∂μ) = 1 :=
    (lintegral_congr_ae ((hFU k).symm.fun_comp (fun u : ℝ≥0 => (u : ℝ≥0∞)^criticalExponent 1 s))).trans (hm k)
  have : (euclideanMeasure n).IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  have hmom k : cubeMoment 1 n s (F k) = cubeMoment 1 n s (U k) := by
    exact congrArg (fun R => ∫⁻ h, R h ^ s ∂cubeMeasure μ 1) (autocorrelation_congr_ae μ (hFU k) 1)
  have hK0 : K ≠ 0 := by dsimp [K]; rw [youngMomentConstant_one]; unfold diagonalYoungFactor; positivity
  have hKt : K ≠ ⊤ := by dsimp [K]; rw [youngMomentConstant_one]; finiteness
  have hqeq : criticalExponent 1 s = q := by simp [criticalExponent,add_comm]
  have hq : 0 < q := by positivity
  have hs1 : 1 < s := by linarith
  apply Metric.tendsto_atTop.2
  intro η hη
  have hη' : 0 < η/2 := by positivity
  obtain ⟨δ,hδ,H⟩ := near_youngEuler n hs1 hη'
  let ε := min (δ/2) (1/2)
  have hε : 0<ε := lt_min (by positivity) (by norm_num)
  have hed : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hcut : ENNReal.ofReal (1-ε) * K < K := by
    conv_rhs => rw [← one_mul K]
    exact (ENNReal.mul_lt_mul_iff_left hK0 hKt).2 (ENNReal.ofReal_lt_one.mpr (by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hJ.eventually (lt_mem_nhds hcut))
  refine ⟨N,fun k hk => ?_⟩
  have hnear := (hmom k) ▸ (hN k hk).le
  have h := H ε hε.le hed (U k) (hU k) (hmass k) hnear
  rw [hqeq,← YoungUnitInput.edist_eq_lpDist hq (hrep k) (youngRealEuler_ae n s hs (f k) (U k) (hrep k))] at h
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hη'.le, ← dist_edist] at hb
  simpa [Real.dist_eq,abs_of_nonneg dist_nonneg] using (hb.trans_lt (by linarith : η/2<η))

end
end LpGowers
