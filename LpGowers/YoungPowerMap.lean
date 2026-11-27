module

public import LpGowers.YoungPowerScalar
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-! Strict Fréchet differentiation of the real signed power between Lebesgue spaces.
For a power greater than one the derivative is multiplication by the
absolute power of one degree less. At degree one the map is the identity. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace LpGowers

variable {X : Type*} [MeasurableSpace X]

private theorem absPower_memLp (μ : Measure X) (p q : ℝ≥0∞) (m : ℝ) (hm : 0 < m)
    (hpq : p=q*ENNReal.ofReal m) (f : Lp ℝ p μ) : MemLp (fun x => |f x|^m) q μ := by
  have hf := Lp.memLp f
  rw [memLp_iff]
  rw [show (fun x => |f x|^m) = fun x => ‖f x‖^m by rfl,
    eLpNorm_norm_rpow _ hf.aestronglyMeasurable hm,← hpq]
  exact (ENNReal.rpow_lt_top_of_nonneg hm.le hf.eLpNorm_ne_top)

private def absPowerLp (μ : Measure X) (p q : ℝ≥0∞) (m : ℝ) (hm : 0<m)
    (hpq : p=q*ENNReal.ofReal m) (f : Lp ℝ p μ) : Lp ℝ q μ :=
  (absPower_memLp μ p q m hm hpq f).toLp _

private theorem absPowerLp_coe (μ : Measure X) (p q : ℝ≥0∞) (m : ℝ) (hm : 0<m)
    (hpq : p=q*ENNReal.ofReal m) (f : Lp ℝ p μ) :
    absPowerLp μ p q m hm hpq f =ᵐ[μ] fun x => |f x|^m := MemLp.coeFn_toLp _

private theorem absPowerLp_norm (μ : Measure X) (p q : ℝ≥0∞) (m : ℝ) (hm : 0<m)
    (hpq : p=q*ENNReal.ofReal m) (f : Lp ℝ p μ) :
    ‖absPowerLp μ p q m hm hpq f‖ = ‖f‖^m := by
  rw [absPowerLp,Lp.norm_toLp,show (fun x => |f x|^m) = fun x => ‖f x‖^m by rfl,
    eLpNorm_norm_rpow _ (Lp.aestronglyMeasurable f) hm, ← hpq,← ENNReal.toReal_rpow,Lp.norm_def]

lemma signedPower_memLp (μ : Measure X) (p q : ℝ≥0∞) (g : ℝ) (hg : 1≤g)
    (hpq : p=q*ENNReal.ofReal g) (f : Lp ℝ p μ) : MemLp (fun x => signedPower g (f x)) q μ := by
  have hc : Continuous (signedPower g) := continuous_iff_continuousAt.2
    (fun t => (hasDerivAt_signedPower hg t).continuousAt)
  apply (absPower_memLp μ p q g (zero_lt_one.trans_le hg) hpq f).mono'
    (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  filter_upwards with x
  rw [Real.norm_eq_abs,signedPower,abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  apply le_of_eq
  simpa [signedPower,abs_of_nonneg (abs_nonneg _)] using signedPower_nonneg_value hg (abs_nonneg (f x))

/-- The real signed power of degree g on Lebesgue classes. -/
def signedPowerLp (μ : Measure X) (p q : ℝ≥0∞) (g : ℝ) (hg : 1≤g)
    (hpq : p=q*ENNReal.ofReal g) (f : Lp ℝ p μ) : Lp ℝ q μ :=
  (signedPower_memLp μ p q g hg hpq f).toLp _

theorem signedPowerLp_coe (μ : Measure X) (p q : ℝ≥0∞) (g : ℝ) (hg : 1≤g)
    (hpq : p=q*ENNReal.ofReal g) (f : Lp ℝ p μ) :
    signedPowerLp μ p q g hg hpq f =ᵐ[μ] fun x => signedPower g (f x) :=
  MemLp.coeFn_toLp _

/-- Strict Fréchet derivative at every signed input, including inputs vanishing on
sets of positive measure. The derivative is specified on equivalence classes. -/
theorem hasStrictFDerivAt_signedPowerLp (μ : Measure X) (p q : ℝ≥0∞) [hp1 : Fact (1≤p)]
    [hq1 : Fact (1≤q)] (g : ℝ) (hg : 1≤g) (hpq : p=q*ENNReal.ofReal g)
    (hqfin : q≠⊤) (f : Lp ℝ p μ) :
    ∃ D : Lp ℝ p μ →L[ℝ] Lp ℝ q μ, HasStrictFDerivAt (signedPowerLp μ p q g hg hpq) D f ∧
      ∀ h, D h =ᵐ[μ] fun x => g*|f x|^(g-1)*h x := by
  rcases hg.eq_or_lt with rfl | hg
  · have h := hpq
    simp only [ENNReal.ofReal_one,mul_one] at h
    cases h
    refine ⟨ContinuousLinearMap.id ℝ _, ?_, fun h => ?_⟩
    · have he : signedPowerLp μ p p 1 le_rfl (by simp) = id := by
        funext t
        apply Lp.ext
        simpa [signedPower] using signedPowerLp_coe μ p p 1 le_rfl (by simp) t
      rw [he]
      exact hasStrictFDerivAt_id f
    · simp
  let m := g-1
  have hm : 0<m := sub_pos.mpr hg
  let w := ENNReal.ofReal (p.toReal/m)
  have hq0 : 0<q.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hq1.out)) hqfin
  have hqr : (1:ℝ) ≤ q.toReal := by simpa using ENNReal.toReal_mono hqfin hq1.out
  have hp : p.toReal = q.toReal*g := by rw [hpq,ENNReal.toReal_mul,ENNReal.toReal_ofReal (zero_lt_one.trans hg).le]
  have hp0 : 0<p.toReal := hp ▸ mul_pos hq0 (zero_lt_one.trans hg)
  have hw : w.toReal = p.toReal/m := ENNReal.toReal_ofReal (div_nonneg hp0.le hm.le)
  have hpw : p=w*ENNReal.ofReal m := by
    have hf : p≠⊤ := by rw [hpq]; exact ENNReal.mul_ne_top hqfin ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_toReal hf]
    dsimp [w]
    rw [← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hm.ne']
  let : Fact (1≤w) := ⟨by
    change 1≤ ENNReal.ofReal (p.toReal/m)
    rw [ENNReal.one_le_ofReal]
    apply (le_div_iff₀ hm).2
    dsimp [m]; rw [hp]; nlinarith [mul_nonneg (sub_nonneg.mpr hqr) (zero_lt_one.trans hg).le]⟩
  let : ENNReal.HolderTriple w p q := ENNReal.HolderTriple.of_toReal
    ⟨by rw [hw,hp]; field_simp; dsimp [m]; ring, by rw [hw]; positivity, hp0⟩
  let T := signedPowerLp μ p q g hg.le hpq
  let A := absPowerLp μ p w m hm hpw
  let B := ContinuousLinearMap.mul ℝ ℝ
  let M := B.holderL μ w p q
  let D : Lp ℝ p μ →L[ℝ] Lp ℝ q μ := g • M (A f)
  have hD (h : Lp ℝ p μ) : D h =ᵐ[μ] fun x => g*|f x|^m*h x := by
    filter_upwards [Lp.coeFn_smul g (M (A f) h),B.coeFn_holder (r:=q) (A f) h,
      absPowerLp_coe μ p w m hm hpw f] with x hx hB hA
    change (g • M (A f) h) x = _
    rw [hx]; change g*(M (A f) h x) = _
    rw [show M (A f) h x = (A f x)*(h x) from hB,hA]; ring
  refine ⟨D,?_, hD⟩
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro e he
  let b := e/(2*(‖f‖^m+1))
  have hb : 0<b := by dsimp [b]; positivity
  obtain ⟨C,hC,hs⟩ := signedPower_strict_remainder hg hb
  have point (u v : Lp ℝ p μ) :
      ‖T u-T v-D (u-v)‖ ≤
      (b*‖f‖^m+C*(‖u-f‖+‖v-f‖)^m)*‖u-v‖ := by
    let d := |u-f| + |v-f|
    let W := b • A f + C • A d
    have h₁ : ‖T u-T v-D (u-v)‖ ≤ ‖M W (u-v)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_sub (T u-T v) (D (u-v)), Lp.coeFn_sub (T u) (T v),
        signedPowerLp_coe μ p q g hg.le hpq u, signedPowerLp_coe μ p q g hg.le hpq v,
        hD (u-v),Lp.coeFn_sub u v,B.coeFn_holder (r:=q) W (u-v),
        Lp.coeFn_add (b • A f) (C • A d),Lp.coeFn_smul b (A f),Lp.coeFn_smul C (A d),
        absPowerLp_coe μ p w m hm hpw f,absPowerLp_coe μ p w m hm hpw d,
        Lp.coeFn_add |u-f| |v-f|,Lp.coeFn_abs (u-f),Lp.coeFn_abs (v-f),
        Lp.coeFn_sub u f,Lp.coeFn_sub v f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇
      change |(T u-T v-D (u-v)) x| ≤ abs (M W (u-v) x)
      change (T u) x = _ at h₃
      change (T v) x = _ at h₄
      change M W (u-v) x = W x * (u-v) x at h₇
      change W x = _ at h₈
      change A f x = _ at h₁₁
      change A d x = _ at h₁₂
      change d x = _ at h₁₃
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply] at h₁ h₂ h₆ h₈ h₉ h₁₀ h₁₃ h₁₆ h₁₇
      rw [h₁,h₂,h₃,h₄,h₅,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,h₁₇,h₆]
      simp only [smul_eq_mul,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ |u x-f x|+|v x-f x| by positivity)]
      rw [abs_of_nonneg (by positivity : 0≤b*|f x|^m+C*(|u x-f x|+|v x-f x|)^m)]
      exact hs (u x) (v x) (f x)
    have h₂ : ‖M W (u-v)‖ ≤ ‖W‖ * ‖u-v‖ := by
      simpa [M,B,ContinuousLinearMap.opNorm_mul] using B.norm_holder_apply_apply_le (r:=q) W (u-v)
    have hd : ‖d‖ ≤ ‖u-f‖+‖v-f‖ := by
      simpa only [d,norm_abs_eq_norm] using (norm_add_le |u-f| |v-f|)
    have h₃ : ‖W‖ ≤ b*‖f‖^m+C*(‖u-f‖+‖v-f‖)^m := by
      calc
        _ ≤ ‖b • A f‖+‖C • A d‖ := norm_add_le _ _
        _ = b*‖f‖^m+C*‖d‖^m := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb.le,abs_of_nonneg hC,
          A,absPowerLp_norm]
        _ ≤ _ := by gcongr
    exact h₁.trans (h₂.trans (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)))
  have hsmall : b*‖f‖^m<e := by
    dsimp [b]; rw [div_mul_eq_mul_div,div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg he.le (Real.rpow_nonneg (norm_nonneg f) m)]
  have hc : ContinuousAt (fun z : Lp ℝ p μ × Lp ℝ p μ =>
    b*‖f‖^m+C*(‖z.1-f‖+‖z.2-f‖)^m) (f,f) := by fun_prop (disch := positivity)
  have hlt : ∀ᶠ z : Lp ℝ p μ × Lp ℝ p μ in 𝓝 (f,f),
      b*‖f‖^m+C*(‖z.1-f‖+‖z.2-f‖)^m<e :=
    hc.eventually_lt continuousAt_const (by simpa [Real.zero_rpow hm.ne'] using hsmall)
  filter_upwards [hlt] with z hz
  exact (point z.1 z.2).trans (mul_le_mul_of_nonneg_right hz.le (norm_nonneg _))

end LpGowers
