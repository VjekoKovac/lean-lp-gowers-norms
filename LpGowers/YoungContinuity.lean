module

public import LpGowers.PhaseRemoval
public import LpGowers.Nonvanishing
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! Mixed Young inequality with constant one, and the perturbation estimate
needed to replace a nearly extremal input by a normalized indicator. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
namespace LpGowers

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant]

omit [μ.IsAddLeftInvariant] in
private theorem corrMeas {F J : G → ℝ≥0∞} (hf : Measurable F) (hg : Measurable J) :
    Measurable (pairCorrelation μ F J) :=
  Measurable.lintegral_prod_right ((hf.comp measurable_snd).mul
    (hg.comp (measurable_snd.add measurable_fst)))

omit [SigmaFinite μ] in
private theorem corr_congr {F F' J J' : G → ℝ≥0∞}
    (hf : F =ᵐ[μ] F') (hg : J =ᵐ[μ] J') : pairCorrelation μ F J = pairCorrelation μ F' J' := by
  funext t
  exact lintegral_congr_ae (hf.mul ((measurePreserving_add_right μ t).quasiMeasurePreserving.ae_eq_comp hg))

private theorem young_norm (d : ℝ) (hd : 1 < d) {F J : G → ℝ≥0∞}
    (hf : Measurable F) (hg : Measurable J) :
    let s := 2*d/(d+1)
    lp μ d (pairCorrelation μ F J) ≤ lp μ s F * lp μ s J := by
  let s := 2*d/(d+1)
  let w := (d-1)/(2*d)
  have hd0 : 0 < d := by linarith
  have hs : 0 < s := div_pos (by positivity) (by linarith)
  have hw : 0 < w := div_pos (by linarith) (by positivity)
  have he : 1/d + w + w = 1 := by dsimp [w]; field_simp; ring
  have hex : s*(1/d) + s*w = 1 := by dsimp [w,s]; field_simp; ring
  let A := ∫⁻ x, F x ^ s ∂μ
  let B := ∫⁻ x, J x ^ s ∂μ
  let C := pairCorrelation μ (fun x => F x ^ s) (fun x => J x ^ s)
  have hC : Measurable C := corrMeas μ (hf.pow_const _) (hg.pow_const _)
  have hInt : ∫⁻ t, C t ∂μ = A * B := by
    dsimp [C, pairCorrelation]
    rw [lintegral_lintegral_swap]
    · calc
        _ = ∫⁻ x, (F x)^s * B ∂μ := by
          apply lintegral_congr; intro x
          rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left_eq_self (fun z => J z ^ s) x]
        _ = _ := lintegral_mul_const _ (hf.pow_const _)
    · exact (((hf.comp measurable_snd).pow_const _).mul
        ((hg.comp (measurable_snd.add measurable_fst)).pow_const _)).aemeasurable
  have hpt (t : G) : pairCorrelation μ F J t ≤ C t ^ (1/d) * A^w * B^w := by
    let a := fun x => F x ^ s
    let b := fun x => J (x+t) ^ s
    have ha : Measurable a := hf.pow_const _
    have hb : Measurable b := (hg.comp (measurable_id.add_const t)).pow_const _
    have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
      (f := ![a * b,a,b]) (p := ![1/d,w,w])
      (fun i _ => by fin_cases i <;> simp [(ha.mul hb).aemeasurable,ha.aemeasurable,hb.aemeasurable])
      (by simpa [Fin.sum_univ_three] using he)
      (fun i _ => by fin_cases i <;> simp [hw.le, hd0.le])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Pi.mul_apply] at h
    have hB : ∫⁻ x, b x ∂μ = B := lintegral_add_right_eq_self (fun x => J x ^ s) t
    rw [hB] at h
    apply le_trans _ (by simpa only [C, A, pairCorrelation, a, b, mul_assoc] using h)
    apply lintegral_mono; intro x
    apply le_of_eq
    dsimp only [a,b]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hd0).le]
    simp only [← ENNReal.rpow_mul]
    calc
      _ = (F x ^ (s*(1/d)) * F x ^ (s*w)) * (J (x+t) ^ (s*(1/d)) * J (x+t) ^ (s*w)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hex, ENNReal.rpow_one,
          ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hex, ENNReal.rpow_one]
      _ = _ := by ac_rfl
  have hraw : (∫⁻ t, (pairCorrelation μ F J t)^d ∂μ) ≤
      A * B * (A^(w*d) * B^(w*d)) := by
    calc
      _ ≤ ∫⁻ t, (C t^(1/d)*A^w*B^w)^d ∂μ := lintegral_mono fun t => ENNReal.rpow_le_rpow (hpt t) hd0.le
      _ = _ := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hd0.le, ← ENNReal.rpow_mul,
          one_div_mul_cancel hd0.ne', ENNReal.rpow_one, mul_assoc]
        rw [lintegral_mul_const _ hC, hInt, mul_assoc]
  apply (ENNReal.rpow_le_rpow hraw (one_div_pos.mpr hd0).le).trans_eq
  have hcollapse : (1 + w*d)*(1/d) = 1/s := by dsimp [s,w]; field_simp; ring
  dsimp only [lp]
  rw [mul_mul_mul_comm A B, ← ENNReal.rpow_one A, ← ENNReal.rpow_one B]
  simp only [← ENNReal.rpow_mul, one_mul]
  rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity),
    ← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hd0).le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, hcollapse]

/-- The mixed correlation estimate on two general inputs with equal
input exponent 2d/(d+1) and output exponent d>1. -/
theorem mixedYoung {d : ℝ} (hd : 1 < d) {F J : G → ℝ≥0∞}
    (hf : AEMeasurable F μ) (hg : AEMeasurable J μ) :
    let s := 2*d/(d+1)
    lp μ d (pairCorrelation μ F J) ≤ lp μ s F * lp μ s J := by
  dsimp only
  rw [corr_congr μ hf.ae_eq_mk hg.ae_eq_mk]
  have normEq {V W : G → ℝ≥0∞} (h : V =ᵐ[μ] W) (s : ℝ) : lp μ s V = lp μ s W := by
    unfold lp
    congr 1
    exact lintegral_congr_ae (h.fun_comp (fun v : ℝ≥0∞ => v^s))
  rw [normEq hf.ae_eq_mk, normEq hg.ae_eq_mk]
  exact young_norm μ d hd hf.measurable_mk hg.measurable_mk

private theorem corr_meas_ae {F J : G → ℝ≥0∞} (hf : AEMeasurable F μ) (hg : AEMeasurable J μ) :
    Measurable (pairCorrelation μ F J) := by
  rw [corr_congr μ hf.ae_eq_mk hg.ae_eq_mk]
  exact corrMeas μ hf.measurable_mk hg.measurable_mk

/-- Perturbing a unit input to diagonal Young changes its output norm by at
most twice the input distance. Applied in both orders this gives continuity. -/
theorem diagonalYoung_lp_le_real (d : ℝ) (hd' : 1 < d) (f g : G → ℝ≥0)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    let s := 2*d/(d+1)
    (∫⁻ x, (f x : ℝ≥0∞)^s ∂μ) = 1 → (∫⁻ x, (g x : ℝ≥0∞)^s ∂μ) = 1 →
    lp μ d (fun a => ∫⁻ x, (f x:ℝ≥0∞) * f (x+a) ∂μ) ≤
      lp μ d (fun a => ∫⁻ x, (g x:ℝ≥0∞) * g (x+a) ∂μ) + 2 * lpDist μ s f g := by
  intro s hfm hgm
  let F := liftNN f
  let J := liftNN g
  let E := fun x => edist (f x) (g x)
  have hF : AEMeasurable F μ := measurable_coe_nnreal_ennreal.comp_aemeasurable hf
  have hJ : AEMeasurable J μ := measurable_coe_nnreal_ennreal.comp_aemeasurable hg
  have hE : AEMeasurable E μ := hf.edist hg
  have tri (x : G) : F x ≤ J x + E x := by
    have h := edist_triangle (f x) (g x) 0
    simpa [F,J,E,liftNN,edist_dist,NNReal.dist_eq,add_comm] using h
  have prod (x t : G) : F x * F (x+t) ≤ J x * J (x+t) + J x * E (x+t) + E x * F (x+t) := by
    calc
      _ ≤ (J x + E x) * F (x+t) := mul_le_mul_left (tri x) _
      _ = J x * F (x+t) + E x * F (x+t) := by rw [add_mul]
      _ ≤ J x * (J (x+t) + E (x+t)) + E x * F (x+t) := by gcongr; exact tri _
      _ = _ := by rw [mul_add]
  have pt (t : G) : pairCorrelation μ F F t ≤
      (pairCorrelation μ J J + pairCorrelation μ J E + pairCorrelation μ E F) t := by
    have hj := hJ.comp_quasiMeasurePreserving (measurePreserving_add_right μ t).quasiMeasurePreserving
    have he := hE.comp_quasiMeasurePreserving (measurePreserving_add_right μ t).quasiMeasurePreserving
    let U := fun x => J x * J (x+t)
    let V := fun x => J x * E (x+t)
    let W := fun x => E x * F (x+t)
    have hU : AEMeasurable U μ := hJ.mul hj
    have hV : AEMeasurable V μ := hJ.mul he
    calc
      _ ≤ ∫⁻ x, (U x + V x) + W x ∂μ := lintegral_mono (fun x => prod x t)
      _ = _ := by
        rw [lintegral_add_left' (f := fun x => U x + V x) (hU.add hV) W, lintegral_add_left' hU V]
        rfl
  have Nf : lp μ s F = 1 := by simp only [lp,F,liftNN,hfm,ENNReal.one_rpow]
  have Ng : lp μ s J = 1 := by simp only [lp,J,liftNN,hgm,ENNReal.one_rpow]
  have C₁ := (corr_meas_ae μ hJ hJ).aemeasurable (μ := μ)
  have C₂ := (corr_meas_ae μ hJ hE).aemeasurable (μ := μ)
  have C₃ := (corr_meas_ae μ hE hF).aemeasurable (μ := μ)
  change lp μ d (pairCorrelation μ F F) ≤ _
  calc
    _ ≤ lp μ d (pairCorrelation μ J J + pairCorrelation μ J E + pairCorrelation μ E F) := by
      unfold lp; gcongr with x; exact pt x
    _ ≤ lp μ d (pairCorrelation μ J J + pairCorrelation μ J E) +
        lp μ d (pairCorrelation μ E F) := ENNReal.lintegral_Lp_add_le (C₁.add C₂) C₃ hd'.le
    _ ≤ lp μ d (pairCorrelation μ J J) + lp μ d (pairCorrelation μ J E) +
        lp μ d (pairCorrelation μ E F) := add_le_add_left (ENNReal.lintegral_Lp_add_le C₁ C₂ hd'.le) _
    _ ≤ lp μ d (pairCorrelation μ J J) + (lp μ s J * lp μ s E) + (lp μ s E * lp μ s F) :=
      add_le_add (add_le_add_right (mixedYoung μ hd' hJ hE) _) (mixedYoung μ hd' hE hF)
    _ = _ := by rw [Nf,Ng,one_mul,mul_one,two_mul,add_assoc]; rfl

/-- Integer-exponent form used by the subgroup stability argument. -/
theorem diagonalYoung_lp_le (d : ℕ) (hd : 2 ≤ d) (f g : G → ℝ≥0)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    let s := 2*(d:ℝ)/(d+1)
    (∫⁻ x, (f x : ℝ≥0∞)^s ∂μ) = 1 → (∫⁻ x, (g x : ℝ≥0∞)^s ∂μ) = 1 →
    lp μ (d:ℝ) (fun a => ∫⁻ x, (f x:ℝ≥0∞) * f (x+a) ∂μ) ≤
      lp μ (d:ℝ) (fun a => ∫⁻ x, (g x:ℝ≥0∞) * g (x+a) ∂μ) + 2 * lpDist μ s f g :=
  diagonalYoung_lp_le_real μ (d : ℝ) (by exact_mod_cast (show 1 < d by omega)) f g hf hg

end LpGowers
