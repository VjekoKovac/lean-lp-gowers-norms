module

public import LpGowers.CorrelationOperator
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! The nonsharp mixed Young inequality needed for differentiability, obtained by
three-factor Hölder and translation invariance. The exponent balance is explicit. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
namespace LpGowers

theorem generalCorrBound (n : ℕ) {p q d : ℝ} (hp : 0<p) (hq : 0<q) (hd0 : 0<d)
    (hpd : p ≤ d) (hqd : q ≤ d) (hbal : 1/p+1/q=1+1/d) : CorrBound n p q d 1 := by
  intro F J hf hg
  rw [one_mul]
  let μ := euclideanMeasure n
  have : SigmaFinite μ := by change SigmaFinite (volume : Measure (Rn n)); infer_instance
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  let u := 1/p-1/d
  let v := 1/q-1/d
  have hu : 0≤u := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpd)
  have hv : 0≤v := sub_nonneg.mpr (one_div_le_one_div_of_le hq hqd)
  have he : 1/d+u+v=1 := by dsimp [u,v]; linarith
  have hexF : p*(1/d)+p*u=1 := by dsimp [u]; field_simp; ring
  have hexJ : q*(1/d)+q*v=1 := by dsimp [v]; field_simp; ring
  let A := ∫⁻ x, F x ^ p ∂μ
  let B := ∫⁻ x, J x ^ q ∂μ
  let C := pairCorrelation μ (fun x => F x ^ p) (fun x => J x ^ q)
  have hC : Measurable C := Measurable.lintegral_prod_right (((hf.comp measurable_snd).pow_const _).mul ((hg.comp (measurable_snd.add measurable_fst)).pow_const _))
  have hInt : ∫⁻ t, C t ∂μ = A * B := by
    dsimp [C, pairCorrelation]
    rw [lintegral_lintegral_swap]
    · calc
        _ = ∫⁻ x, (F x)^p * B ∂μ := by
          apply lintegral_congr; intro x
          rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left_eq_self (fun z => J z ^ q) x]
        _ = _ := lintegral_mul_const _ (hf.pow_const _)
    · exact (((hf.comp measurable_snd).pow_const _).mul
        ((hg.comp (measurable_snd.add measurable_fst)).pow_const _)).aemeasurable
  have hpt (t : Rn n) : pairCorrelation μ F J t ≤ C t ^ (1/d) * A^u * B^v := by
    let a := fun x => F x ^ p
    let b := fun x => J (x+t) ^ q
    have ha : Measurable a := hf.pow_const _
    have hb : Measurable b := (hg.comp (measurable_id.add_const t)).pow_const _
    have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin 3))
      (f := ![a * b,a,b]) (p := ![1/d,u,v])
      (fun i _ => by fin_cases i <;> simp [(ha.mul hb).aemeasurable,ha.aemeasurable,hb.aemeasurable])
      (by simpa [Fin.sum_univ_three] using he)
      (fun i _ => by fin_cases i <;> simp [hu, hv, hd0.le])
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Pi.mul_apply] at h
    have hB : ∫⁻ x, b x ∂μ = B := lintegral_add_right_eq_self (fun x => J x ^ q) t
    rw [hB] at h
    apply le_trans _ (by simpa only [C, A, pairCorrelation, a, b, mul_assoc] using h)
    apply lintegral_mono; intro x
    apply le_of_eq
    dsimp only [a,b]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hd0).le]
    simp only [← ENNReal.rpow_mul]
    calc
      _ = (F x ^ (p*(1/d)) * F x ^ (p*u)) * (J (x+t) ^ (q*(1/d)) * J (x+t) ^ (q*v)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hexF, ENNReal.rpow_one,
          ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hexJ, ENNReal.rpow_one]
      _ = _ := by ac_rfl
  have hraw : (∫⁻ t, (pairCorrelation μ F J t)^d ∂μ) ≤
      A * B * (A^(u*d) * B^(v*d)) := by
    calc
      _ ≤ ∫⁻ t, (C t^(1/d)*A^u*B^v)^d ∂μ := lintegral_mono fun t => ENNReal.rpow_le_rpow (hpt t) hd0.le
      _ = _ := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hd0.le, ← ENNReal.rpow_mul,
          one_div_mul_cancel hd0.ne', ENNReal.rpow_one, mul_assoc]
        rw [lintegral_mul_const _ hC, hInt, mul_assoc]
  apply (ENNReal.rpow_le_rpow hraw (one_div_pos.mpr hd0).le).trans_eq
  have hcollapseF : (1 + u*d)*(1/d) = 1/p := by dsimp [u]; field_simp; ring
  have hcollapseJ : (1 + v*d)*(1/d) = 1/q := by dsimp [v]; field_simp; ring
  dsimp only [lp]
  rw [mul_mul_mul_comm A B, ← ENNReal.rpow_one A, ← ENNReal.rpow_one B]
  simp only [← ENNReal.rpow_mul, one_mul]
  rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity),
    ← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hd0).le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, hcollapseF,hcollapseJ]

/-- For the two Lᵖ convolution operators in the Young update, the sharp
inverse argument only needs boundedness to differentiate them. -/
theorem firstUpdateBound (n : ℕ) (s : ℝ) (hs : 1<s) :
    CorrBound n (2*s/(s+1)) (2*s/(s+1)) s 1 := by
  have hs0 := zero_lt_one.trans hs
  have hp : 0<2*s/(s+1) := by positivity
  have hps : 2*s/(s+1) ≤ s := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  apply generalCorrBound n hp hp hs0 hps hps
  field_simp
  ring

theorem secondUpdateBound (n : ℕ) (s : ℝ) (hs : 1<s) :
    CorrBound n (s/(s-1)) (2*s/(s+1)) (2*s/(s-1)) 1 := by
  have hs0 := zero_lt_one.trans hs
  have hs1 : 0<s-1 := sub_pos.mpr hs
  have hp : 0<s/(s-1) := div_pos hs0 hs1
  have hq : 0<2*s/(s+1) := by positivity
  have hr : 0<2*s/(s-1) := by positivity
  apply generalCorrBound n hp hq hr
  · gcongr
    linarith
  · exact div_le_div_of_nonneg_left (by positivity) hs1 (by linarith)
  · field_simp
    ring

/-- Bounded real-bilinear first correlation of the nonlinear Young update. -/
def diagonalCorrCLM (n : ℕ) (s : ℝ) (hs : 1<s)
    [Fact (1≤ENNReal.ofReal (2*s/(s+1)))] [Fact (1≤ENNReal.ofReal s)] :
    EuclideanLp n (2*s/(s+1)) →L[ℝ] EuclideanLp n (2*s/(s+1)) →L[ℝ] EuclideanLp n s :=
  corrCLM (by have := zero_lt_one.trans hs; positivity) (by have := zero_lt_one.trans hs; positivity)
    (zero_lt_one.trans hs) ENNReal.one_ne_top (firstUpdateBound n s hs)

/-- Bounded real-bilinear adjoint correlation of the nonlinear Young update. -/
def adjointCorrCLM (n : ℕ) (s : ℝ) (hs : 1<s)
    [Fact (1≤ENNReal.ofReal (s/(s-1)))] [Fact (1≤ENNReal.ofReal (2*s/(s+1)))]
    [Fact (1≤ENNReal.ofReal (2*s/(s-1)))] :
    EuclideanLp n (s/(s-1)) →L[ℝ] EuclideanLp n (2*s/(s+1)) →L[ℝ] EuclideanLp n (2*s/(s-1)) :=
  corrCLM (div_pos (zero_lt_one.trans hs) (sub_pos.mpr hs)) (by have := zero_lt_one.trans hs; positivity)
    (div_pos (by linarith) (sub_pos.mpr hs)) ENNReal.one_ne_top (secondUpdateBound n s hs)

theorem diagonalCorrCLM_ae (n : ℕ) (s : ℝ) (hs : 1<s)
    [Fact (1≤ENNReal.ofReal (2*s/(s+1)))] [Fact (1≤ENNReal.ofReal s)]
    (f g : EuclideanLp n (2*s/(s+1))) :
    ⇑(diagonalCorrCLM n s hs f g) =ᵐ[euclideanMeasure n] realCorrelation f g :=
  corrCLM_ae _ _ _ _ _ f g

theorem adjointCorrCLM_ae (n : ℕ) (s : ℝ) (hs : 1<s)
    [Fact (1≤ENNReal.ofReal (s/(s-1)))] [Fact (1≤ENNReal.ofReal (2*s/(s+1)))]
    [Fact (1≤ENNReal.ofReal (2*s/(s-1)))] (f : EuclideanLp n (s/(s-1)))
    (g : EuclideanLp n (2*s/(s+1))) :
    ⇑(adjointCorrCLM n s hs f g) =ᵐ[euclideanMeasure n] realCorrelation f g :=
  corrCLM_ae _ _ _ _ _ f g

end LpGowers
