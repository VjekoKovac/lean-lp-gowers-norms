module

public import LpGowers.SharpEuclidean
public import LpGowers.YoungDualNear
import Mathlib.Tactic

/-! # The unit sharp Young Euler operator on nonnegative inputs

Sharp trilinear Young bounds its dual score. Integrating that score against
the input gives the ratio of the input moment to the sharp moment. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace LpGowers

/-- Normalized duality for an extended nonnegative score. Truncated powers
on a finite-measure exhaustion allow the dual score to be unbounded. -/
theorem conjugate_mass_le_one {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {q v : ℝ} (hq : 1 < q) (hv : 1 < v) (hpow : (v-1)*q=v)
    (B : X → ℝ≥0∞) (hB : Measurable B)
    (hdual : ∀ T : X → ℝ≥0∞, Measurable T → ∫⁻ x, T x * B x ∂μ ≤ lp μ q T) :
    ∫⁻ x, B x ^ v ∂μ ≤ 1 := by
  classical
  let U := fun (n : ℕ) => (spanningSets μ n).indicator (fun x => min (B x) (n : ℝ≥0∞))
  have hU n : Measurable (U n) := (hB.min measurable_const).indicator (measurableSet_spanningSets _ _)
  have hle n x : U n x ≤ B x := by
    by_cases h : x ∈ spanningSets μ n
    · simp [U,h]
    · simp [U,h]
  have hv0 := zero_lt_one.trans hv
  have hv1 := sub_pos.mpr hv
  have hfinite n : (∫⁻ x, U n x ^ v ∂μ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (n:ℝ≥0∞)^v * μ (spanningSets μ n))
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hv0.le (by simp))
        (measure_spanningSets_lt_top μ n).ne)
    rw [← lintegral_indicator_const (measurableSet_spanningSets μ n)]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ spanningSets μ n
    · simpa only [U,Set.indicator_of_mem hx] using ENNReal.rpow_le_rpow
        (min_le_right (B x) (n:ℝ≥0∞)) hv0.le
    · simp [U,hx,ENNReal.zero_rpow_of_pos hv0]
  have bound n : (∫⁻ x, U n x ^ v ∂μ) ≤ 1 := by
    let T := fun x => U n x ^ (v-1)
    have h := hdual T ((hU n).pow_const _)
    have hh : (∫⁻ x, U n x ^ v ∂μ) ≤ ∫⁻ x, T x * B x ∂μ := by
      apply lintegral_mono
      intro x
      calc
        _ = U n x ^ (v-1) * U n x := by
          nth_rw 2 [← ENNReal.rpow_one (U n x)]
          rw [← ENNReal.rpow_add_of_nonneg _ _ hv1.le zero_le_one]
          ring_nf
        _ ≤ _ := mul_le_mul_right (hle n x) _
    have hn := hh.trans h
    simp only [lp,T,← ENNReal.rpow_mul,hpow] at hn
    by_contra! hn'
    have hlt := ENNReal.rpow_lt_rpow_of_exponent_lt hn' (hfinite n)
      ((div_lt_iff₀ (zero_lt_one.trans hq)).2 (by simpa using hq) : 1/q<1)
    exact (not_lt_of_ge hn) (by simpa using hlt)
  apply le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((hU n).pow_const v).aemeasurable) ?_ ?_) bound
  · apply ae_of_all; intro x i j hij
    apply ENNReal.rpow_le_rpow _ hv0.le
    by_cases hi : x ∈ spanningSets μ i
    · have hj := (monotone_spanningSets μ hij) hi
      simpa [U,hi,hj] using min_le_min_left (B x) (show (i:ℝ≥0∞) ≤ j by exact_mod_cast hij)
    · simp [U,hi]
  · apply ae_of_all; intro x
    apply Filter.Tendsto.ennrpow_const v
    have ht := (tendsto_const_nhds (x := B x)).min ENNReal.tendsto_nat_nhds_top
    apply (show Tendsto (fun n : ℕ => min (B x) n) atTop (𝓝 (B x)) by simpa using ht).congr'
    filter_upwards [eventually_mem_spanningSets μ x] with n hn
    simp [U,hn]

/-- The adjoint dual input paired with a near-extremizer. The normalization
uses the fixed sharp s-th moment, independently of the chosen input. -/
def sharpYoungScore (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0) (x : Rn n) : ℝ≥0∞ :=
  let μ := euclideanMeasure n
  let R := pairCorrelation μ (liftNN F) (liftNN F)
  (youngMomentConstant 1 n s)⁻¹ * ∫⁻ t, (R t)^(s-1) * F (x+t) ∂μ

/-- Pointwise nonnegative representative of the normalized Euler update.
The dual representative is finite almost everywhere on normalized inputs. -/
def youngEuler (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0) (x : Rn n) : ℝ≥0 :=
  (sharpYoungScore n s F x).toNNReal ^ (2*s/(s-1)-1)

private theorem measurable_corr (n : ℕ) (F G : Rn n → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) :
    Measurable (pairCorrelation (euclideanMeasure n) F G) := by
  let : SigmaFinite (euclideanMeasure n) := by unfold euclideanMeasure; infer_instance
  exact Measurable.lintegral_prod_right ((hF.comp measurable_snd).mul
    (hG.comp (measurable_snd.add measurable_fst)))

theorem measurable_sharpYoungScore (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0) (hF : Measurable F) :
    Measurable (sharpYoungScore n s F) := by
  let : SigmaFinite (euclideanMeasure n) := by unfold euclideanMeasure; infer_instance
  unfold sharpYoungScore
  exact measurable_const.mul (Measurable.lintegral_prod_right
    ((((measurable_corr n _ _ hF.coe_nnreal_ennreal hF.coe_nnreal_ennreal).comp
      measurable_snd).pow_const _).mul (hF.coe_nnreal_ennreal.comp (measurable_fst.add measurable_snd))))

/-- Testing the score in the first variable recovers the trilinear Young pairing. -/
theorem pair_sharpYoungScore (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0) (hF : Measurable F)
    (T : Rn n → ℝ≥0∞) (hT : Measurable T) :
    let μ := euclideanMeasure n
    let R := pairCorrelation μ (liftNN F) (liftNN F)
    (∫⁻ x, T x * sharpYoungScore n s F x ∂μ) =
      (youngMomentConstant 1 n s)⁻¹ * ∫⁻ t, pairCorrelation μ T (liftNN F) t * (R t)^(s-1) ∂μ := by
  intro μ R
  let K := youngMomentConstant 1 n s
  let : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have hR := measurable_corr n _ _ hF.coe_nnreal_ennreal hF.coe_nnreal_ennreal
  have point (x) : T x * sharpYoungScore n s F x =
      K⁻¹ * ∫⁻ t, T x * liftNN F (x+t) * (R t)^(s-1) ∂μ := by
    change T x * (K⁻¹ * ∫⁻ t, (R t)^(s-1) * liftNN F (x+t) ∂μ) = _
    rw [mul_left_comm, ← lintegral_const_mul (μ := μ) (f := fun t => R t^(s-1) * liftNN F (x+t))
      (T x) ((hR.pow_const _).mul (hF.coe_nnreal_ennreal.comp (measurable_const_add x)))]
    congr 1
    apply lintegral_congr; intro t
    unfold liftNN
    ac_rfl
  simp_rw [point]
  rw [lintegral_const_mul _ (Measurable.lintegral_prod_right
    ((hT.comp measurable_fst).mul (hF.coe_nnreal_ennreal.comp (measurable_fst.add measurable_snd))
      |>.mul ((hR.comp measurable_snd).pow_const _)))]
  congr 1
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr; intro t
    rw [lintegral_mul_const (μ := μ) (f := fun x => T x * liftNN F (x+t)) (R t ^ (s-1)) (hT.mul (hF.coe_nnreal_ennreal.comp (measurable_id.add_const t)))]
    rfl
  · exact (((hT.comp measurable_fst).mul (hF.coe_nnreal_ennreal.comp
        (measurable_fst.add measurable_snd))).mul ((hR.comp measurable_snd).pow_const _)).aemeasurable

private theorem normed_score_properties (n : ℕ) {s : ℝ} (hs : 1 < s) (F : Rn n → ℝ≥0)
    (hF : Measurable F)
    (hunit : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1) :
    let μ := euclideanMeasure n
    (∫⁻ x, (sharpYoungScore n s F x)^(2*s/(s-1)) ∂μ) ≤ 1 ∧
    (∫⁻ x, (F x : ℝ≥0∞) * sharpYoungScore n s F x ∂μ) =
      (youngMomentConstant 1 n s)⁻¹ * cubeMoment 1 n s F := by
  intro μ
  let : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  let q := 2*s/(s+1)
  let v := 2*s/(s-1)
  let r := s/(s-1)
  let K := youngMomentConstant 1 n s
  let R := pairCorrelation μ (liftNN F) (liftNN F)
  let H := fun t => (R t)^(s-1)
  let J := ∫⁻ t, (R t)^s ∂μ
  have hq : 1 < q := (lt_div_iff₀ (show 0<s+1 by linarith)).2 (by linarith)
  have hv : 1 < v := (lt_div_iff₀ (sub_pos.mpr hs)).2 (by linarith)
  have hr : 0 < r := div_pos (zero_lt_one.trans hs) (sub_pos.mpr hs)
  have hs0 := zero_lt_one.trans hs
  have hr' : (s-1)*r=s := by dsimp [r]; field_simp
  have hq' : criticalExponent 1 s = q := by simp [q,criticalExponent,add_comm]
  have hK : K ≠ 0 := by dsimp [K]; rw [youngMomentConstant_one]; unfold diagonalYoungFactor; positivity
  have hKt : K ≠ ⊤ := by dsimp [K]; rw [youngMomentConstant_one]; finiteness
  have hF' := hF.coe_nnreal_ennreal
  have hR := measurable_corr n _ _ hF' hF'
  have hJ : J ≤ K := by
    have h := sharp_diagonal_young n s hs.le F hF
    rw [hq'] at hunit
    simpa only [J,R,pairCorrelation,liftNN,μ,K,youngMomentConstant_one,hunit,
      ENNReal.one_rpow,mul_one,q] using h
  have hH : lp μ r H ≤ K^(1/r) := by
    simpa [lp,H,← ENNReal.rpow_mul,hr',J] using ENNReal.rpow_le_rpow hJ (one_div_nonneg.mpr hr.le)
  have hN : lp μ q (liftNN F) = 1 := by simp only [lp, liftNN, ← hq',μ,hunit, ENNReal.one_rpow]
  constructor
  · apply conjugate_mass_le_one μ hq hv (by dsimp [q,v]; field_simp; ring)
      _ (measurable_sharpYoungScore n s F hF)
    intro T hT
    rw [pair_sharpYoungScore n s F hF T hT]
    have Htri := sharpYoungTrilinear_of_frame n (young_frame_bound n) s hs T (liftNN F) H hT hF' (hR.pow_const _)
    change (∫⁻ t, pairCorrelation μ T (liftNN F) t * H t ∂μ) ≤ _ at Htri
    change K⁻¹ * (∫⁻ t, pairCorrelation μ T (liftNN F) t * H t ∂μ) ≤ _
    change _ ≤ (ENNReal.ofReal (diagonalYoungFactor s)^n)^(1/s) * lp μ q T * lp μ q (liftNN F) * lp μ r H at Htri
    rw [hN,mul_one,← youngMomentConstant_one] at Htri
    calc
      _ ≤ K⁻¹ * ((K^(1/s)*lp μ q T)*K^(1/r)) :=
        mul_le_mul_right (Htri.trans (mul_le_mul_right hH _)) _
      _ = (K⁻¹*(K^(1/s)*K^(1/r)))*lp μ q T := by ac_rfl
      _ = lp μ q T := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
          show 1/s+1/r=1 by dsimp [r]; field_simp; ring,ENNReal.rpow_one,ENNReal.inv_mul_cancel hK hKt,one_mul]
  · change (∫⁻ x, liftNN F x * sharpYoungScore n s F x ∂euclideanMeasure n) = _
    rw [pair_sharpYoungScore n s F hF (liftNN F) hF',cubeMoment_one n s F hF.aemeasurable]
    congr 1
    apply lintegral_congr; intro t
    change R t * (R t)^(s-1) = (R t)^s
    calc
      _ = (R t)^(1:ℝ) * (R t)^(s-1) := by rw [ENNReal.rpow_one]
      _ = _ := by rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_pos.mpr hs).le]; congr 1; ring

/-- Relative near optimality for the actual sharp autocorrelation moment makes
the input an approximate fixed point of its explicit nonlinear Euler map. -/
theorem near_youngEuler (n : ℕ) {s : ℝ} (hs : 1 < s) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ F : Rn n → ℝ≥0, Measurable F →
      (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1 →
      ENNReal.ofReal (1-ε)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s F →
      lpDist (euclideanMeasure n) (criticalExponent 1 s) F (youngEuler n s F) ≤ ENNReal.ofReal η := by
  let μ := euclideanMeasure n
  let q := criticalExponent 1 s
  let v := 2*s/(s-1)
  let K := youngMomentConstant 1 n s
  have hqeq : q = 2*s/(s+1) := by simp [q,criticalExponent,add_comm]
  have hq : 1 < q := hqeq ▸ (lt_div_iff₀ (show 0<s+1 by linarith)).2 (by linarith)
  have hv : 1 < v := (lt_div_iff₀ (sub_pos.mpr hs)).2 (by linarith)
  have hc : 1/q + 1/v = 1 := by rw [hqeq]; dsimp [v]; field_simp; ring
  have hK0 : K ≠ 0 := by dsimp [K]; rw [youngMomentConstant_one]; unfold diagonalYoungFactor; positivity
  have hKt : K ≠ ⊤ := by dsimp [K]; rw [youngMomentConstant_one]; finiteness
  obtain ⟨δ,hδ,H⟩ := near_norming_power hq hv hc hη
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ F hF hmass hnear
  let S := sharpYoungScore n s F
  let B := fun x => (S x).toNNReal
  have hS : Measurable S := measurable_sharpYoungScore n s F hF
  have hB : Measurable B := hS.ennreal_toNNReal
  obtain ⟨hSm,hpair⟩ := normed_score_properties n hs F hF hmass
  have hfin := ae_lt_top' ((hS.pow_const v).aemeasurable (μ := μ)) (hSm.trans_lt ENNReal.one_lt_top).ne
  have ha : liftNN B =ᵐ[μ] S := by
    filter_upwards [hfin] with x hx
    exact ENNReal.coe_toNNReal (fun he => (by simp [he,ENNReal.top_rpow_of_pos (zero_lt_one.trans hv)] at hx : False))
  have h1 : (∫⁻ x, (B x : ℝ≥0∞)^v ∂μ) ≤ 1 := by
    refine (lintegral_congr_ae ?_).trans_le hSm
    exact ha.fun_comp fun u => u^v
  have h2 : ENNReal.ofReal (1-ε) ≤ (∫⁻ x, (F x : ℝ≥0∞) * B x ∂μ) := by
    have hInt : (∫⁻ x, (F x : ℝ≥0∞) * B x ∂μ) = ∫⁻ x, (F x : ℝ≥0∞) * S x ∂μ := by
      apply lintegral_congr_ae
      exact (Filter.EventuallyEq.rfl : liftNN F =ᵐ[μ] liftNN F).mul ha
    rw [hInt,hpair]
    have hh := mul_le_mul_right hnear K⁻¹
    change K⁻¹ * (_*K) ≤ K⁻¹ * _ at hh
    rwa [mul_left_comm,ENNReal.inv_mul_cancel hK0 hKt,mul_one] at hh
  exact H ε hε hεδ μ F B hF.aemeasurable hB.aemeasurable hmass.le h1 h2

end LpGowers
