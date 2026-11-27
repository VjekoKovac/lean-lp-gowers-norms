module

public import LpGowers.CorrelationDefs

/-! # Signed correlation as a bounded bilinear map on real Euclidean Lᵖ -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers
section
variable {n : ℕ} {p q r : ℝ} {K : ℝ≥0∞}
local notation "ν" => euclideanMeasure n

def realCorrelation (f g : Rn n → ℝ) (t : Rn n) : ℝ := ∫ y, f y*g (y+t) ∂ν

theorem measurable_realCorrelation {f g : Rn n → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (realCorrelation f g) := by
  have : SFinite ν := by change SFinite (volume : Measure (Rn n)); infer_instance
  apply StronglyMeasurable.measurable
  exact ((hf.comp measurable_snd).mul (hg.comp (measurable_snd.add measurable_fst))).stronglyMeasurable.integral_prod_right'

theorem ae_corr_integrable (hp : 0<p) (hq : 0<q) (hr : 0<r) (hK : K ≠ ⊤)
    (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q) :
    ∀ᵐ t ∂ν, Integrable (fun y => f y*g (y+t)) ν := by
  let A := pairCorrelation ν (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ)
  have : SFinite ν := by change SFinite (volume : Measure (Rn n)); infer_instance
  have hA : Measurable A := Measurable.lintegral_prod_right
    (((Lp.stronglyMeasurable f).measurable.eNorm.comp measurable_snd).mul
      ((Lp.stronglyMeasurable g).measurable.eNorm.comp (measurable_snd.add measurable_fst)))
  have h := hY _ _ (Lp.stronglyMeasurable f).measurable.eNorm (Lp.stronglyMeasurable g).measurable.eNorm
  rw [← eLpNorm_eq_lp_real (Lp.aestronglyMeasurable f) hp, ← eLpNorm_eq_lp_real (Lp.aestronglyMeasurable g) hq] at h
  have ht : lp ν r A ≠ ⊤ :=
    (h.trans_lt ((ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (Lp.memLp f).eLpNorm_lt_top.ne)
      (Lp.memLp g).eLpNorm_lt_top.ne).lt_top)).ne
  have hI : (∫⁻ t, A t ^ r ∂ν) ≠ ⊤ := by
    intro H
    exact ht (by rw [lp, H, ENNReal.top_rpow_of_pos (one_div_pos.mpr hr)])
  filter_upwards [ae_lt_top (hA.pow_const r) hI] with t ht'
  have hAt : A t ≠ ⊤ := by
    intro H
    simp [H, ENNReal.top_rpow_of_pos hr] at ht'
  refine ⟨((Lp.stronglyMeasurable f).measurable.mul ((Lp.stronglyMeasurable g).measurable.comp
    (measurable_id.add_const t))).aestronglyMeasurable, ?_⟩
  simpa only [hasFiniteIntegral_iff_eNorm, eNorm_mul, pairCorrelation] using (show pairCorrelation ν (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) t < ⊤ from hAt.lt_top)

theorem signedCorrBound (hp : 0<p) (hq : 0<q) (hr : 0<r) (hY : CorrBound n p q r K)
    (f : EuclideanLp n p) (g : EuclideanLp n q) :
    eLpNorm (realCorrelation f g) (ENNReal.ofReal r) ν ≤
      K * eLpNorm f (ENNReal.ofReal p) ν * eLpNorm g (ENNReal.ofReal q) ν := by
  rw [eLpNorm_eq_lp_real (measurable_realCorrelation (Lp.stronglyMeasurable f).measurable
      (Lp.stronglyMeasurable g).measurable).aestronglyMeasurable hr,
    eLpNorm_eq_lp_real (Lp.aestronglyMeasurable f) hp, eLpNorm_eq_lp_real (Lp.aestronglyMeasurable g) hq]
  refine le_trans ?_ (hY _ _ (Lp.stronglyMeasurable f).measurable.eNorm (Lp.stronglyMeasurable g).measurable.eNorm)
  unfold lp
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hr.le)
  apply lintegral_mono
  intro t
  apply ENNReal.rpow_le_rpow _ hr.le
  simpa only [realCorrelation,pairCorrelation,eNorm_mul] using
    (eNorm_integral_le_lintegral_eNorm (μ := ν) (fun y => f y*g (y+t)))

theorem realCorrelation_mem (hp : 0<p) (hq : 0<q) (hr : 0<r) (hK : K ≠ ⊤)
    (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q) :
    MemLp (realCorrelation f g) (ENNReal.ofReal r) ν :=
  (signedCorrBound hp hq hr hY f g).trans_lt
      ((ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (Lp.memLp f).eLpNorm_lt_top.ne) (Lp.memLp g).eLpNorm_lt_top.ne).lt_top)

def corrValue (hp : 0<p) (hq : 0<q) (hr : 0<r) (hK : K ≠ ⊤)
    (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q) : EuclideanLp n r :=
  (realCorrelation_mem hp hq hr hK hY f g).toLp _

theorem corrValue_ae (hp : 0<p) (hq : 0<q) (hr : 0<r) (hK : K ≠ ⊤)
    (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q) :
    ⇑(corrValue hp hq hr hK hY f g) =ᵐ[ν] realCorrelation f g := MemLp.coeFn_toLp _

theorem realCorrelation_congr {f f' g g' : Rn n → ℝ}
    (hf : f =ᵐ[ν] f') (hg : g =ᵐ[ν] g') (t : Rn n) :
    realCorrelation f g t = realCorrelation f' g' t := by
  have : (euclideanMeasure n).IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  apply integral_congr_ae
  exact hf.mul ((measurePreserving_add_right ν t).quasiMeasurePreserving.ae_eq_comp hg)

/-- Real correlation induced by a quantified Young bound on nonnegative rows. -/
def corrCLM [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal r)] (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hK : K ≠ ⊤) (hY : CorrBound n p q r K) :
    EuclideanLp n p →L[ℝ] EuclideanLp n q →L[ℝ] EuclideanLp n r := by
  let V := corrValue hp hq hr hK hY
  have hv := corrValue_ae hp hq hr hK hY
  have hi := ae_corr_integrable hp hq hr hK hY
  let B : EuclideanLp n p →ₗ[ℝ] EuclideanLp n q →ₗ[ℝ] EuclideanLp n r :=
    LinearMap.mk₂ ℝ V (by
      intro f j g
      apply Lp.ext
      filter_upwards [hv (f+j) g, hv f g, hv j g, Lp.coeFn_add (V f g) (V j g), hi f g, hi j g]
        with t ha hb hc he hI hJ
      rw [he, Pi.add_apply, ha, hb, hc, realCorrelation_congr (Lp.coeFn_add f j) (Filter.EventuallyEq.rfl) t]
      simp only [realCorrelation,Pi.add_apply,add_mul,integral_add hI hJ]) (by
      intro c f g
      apply Lp.ext
      filter_upwards [hv (c • f) g, hv f g, Lp.coeFn_smul c (V f g)] with t ha hb he
      rw [he, Pi.smul_apply, ha, hb, realCorrelation_congr (Lp.coeFn_smul c f) (Filter.EventuallyEq.rfl) t]
      simp only [realCorrelation,Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]) (by
      intro f g j
      apply Lp.ext
      filter_upwards [hv f (g+j), hv f g, hv f j, Lp.coeFn_add (V f g) (V f j), hi f g, hi f j]
        with t ha hb hc he hI hJ
      rw [he, Pi.add_apply, ha, hb, hc, realCorrelation_congr (Filter.EventuallyEq.rfl) (Lp.coeFn_add g j) t]
      simp only [realCorrelation,Pi.add_apply,mul_add,integral_add hI hJ]) (by
      intro c f g
      apply Lp.ext
      filter_upwards [hv f (c • g), hv f g, Lp.coeFn_smul c (V f g)] with t ha hb he
      rw [he, Pi.smul_apply, ha, hb, realCorrelation_congr (Filter.EventuallyEq.rfl) (Lp.coeFn_smul c g) t]
      simp only [realCorrelation,Pi.smul_apply,smul_eq_mul]
      simp_rw [mul_left_comm (f _) c, integral_const_mul])
  apply B.mkContinuous₂ K.toReal
  intro f g
  change ‖(realCorrelation_mem hp hq hr hK hY f g).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, Lp.norm_def]
  simpa only [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (Lp.memLp f).ne) (Lp.memLp g).ne)
      (signedCorrBound hp hq hr hY f g)

theorem corrCLM_ae [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal r)] (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hK : K ≠ ⊤) (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q) :
    ⇑(corrCLM hp hq hr hK hY f g) =ᵐ[ν] realCorrelation f g := corrValue_ae hp hq hr hK hY f g

/-- Every available bound can be applied to the same real bilinear operator. -/
theorem corrCLM_norm_le [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal r)] (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hK : K ≠ ⊤) (hY : CorrBound n p q r K) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hsharp : CorrBound n p q r C) (f : EuclideanLp n p) (g : EuclideanLp n q) :
    ‖corrCLM hp hq hr hK hY f g‖ ≤ C.toReal * ‖f‖ * ‖g‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (corrCLM_ae hp hq hr hK hY f g), Lp.norm_def, Lp.norm_def]
  simpa only [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC (Lp.memLp f).ne) (Lp.memLp g).ne)
      (signedCorrBound hp hq hr hsharp f g)

/-- Comparison with nonnegative measurable representatives. The extended integral is
finite almost everywhere, including when either representative takes exceptional
infinite values on a null set. -/
theorem corrCLM_nonnegative_ae [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal r)] (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hK : K ≠ ⊤) (hY : CorrBound n p q r K) (f : EuclideanLp n p) (g : EuclideanLp n q)
    {F G : Rn n → ℝ≥0∞} (hf : (0 : Rn n → ℝ) ≤ᵐ[ν] ⇑f) (hg : (0 : Rn n → ℝ) ≤ᵐ[ν] ⇑g)
    (hF : (fun x => ENNReal.ofReal (f x)) =ᵐ[ν] F)
    (hG : (fun x => ENNReal.ofReal (g x)) =ᵐ[ν] G) :
    ∀ᵐ t ∂ν, pairCorrelation ν F G t ≠ ⊤ ∧
      corrCLM hp hq hr hK hY f g t = (pairCorrelation ν F G t).toReal := by
  have : (euclideanMeasure n).IsAddRightInvariant := by
    change (volume : Measure (Rn n)).IsAddRightInvariant
    infer_instance
  filter_upwards [corrCLM_ae hp hq hr hK hY f g, ae_corr_integrable hp hq hr hK hY f g] with t ht hi
  have hg' := (measurePreserving_add_right ν t).quasiMeasurePreserving.ae hg
  have hG' := (measurePreserving_add_right ν t).quasiMeasurePreserving.ae_eq_comp hG
  have hpos : 0 ≤ᵐ[ν] (fun y => f y * g (y+t)) := by
    filter_upwards [hf,hg'] with y hfy hgy using mul_nonneg hfy hgy
  have h := ofReal_integral_eq_lintegral_ofReal hi hpos
  have hval : ENNReal.ofReal (realCorrelation f g t) = pairCorrelation ν F G t := by
    apply h.trans
    apply lintegral_congr_ae
    filter_upwards [hf,hF,hG'] with y hfy hFy hGy
    rw [ENNReal.ofReal_mul hfy,← hFy]
    change _ * _ = _ * G (y+t)
    rw [show G (y+t) = ENNReal.ofReal (g (y+t)) from hGy.symm]
  refine ⟨hval ▸ ENNReal.ofReal_ne_top, ?_⟩
  rw [ht,← hval]
  exact (ENNReal.toReal_ofReal (show 0 ≤ realCorrelation f g t from integral_nonneg_of_ae hpos)).symm

end
end LpGowers
