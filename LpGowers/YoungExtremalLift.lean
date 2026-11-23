module

public import LpGowers.SharpEuclidean
public import LpGowers.YoungDuality
public import LpGowers.EuclideanInverse
public import LpGowers.YoungHeatEquality

/-! # Lifting the diagonal Young deficit to the geometric datum

At unit input mass the nonlinear dual test is the first autocorrelation
to the power `s-1`. Both changes of variables in the sharp trilinear
estimate are identities. If the diagonal moment is at least `1-α` times its
optimal value, the real integrable three-input datum attains a ratio at
least `(1-α)^(1/s)`. At equality the heat score of the repeated input is affine.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace LpGowers

/-- The actual density for the repeated input of the geometric datum. -/
def youngFirstDensity (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0) (y : YoungHilbert n) : ℝ :=
  (F (WithLp.ofLp y) : ℝ)^(criticalExponent 1 s)

private theorem frame_lower_toReal {n : ℕ} {s : ℝ} (U : Fin 3 → YoungHilbert n → ℝ≥0∞)
    (hU : ∀ i, Measurable (U i)) (hfin : ∀ i, (∫⁻ y, U i y) ≠ ⊤)
    (c : ℝ≥0∞) (hE : c*∏ i, (∫⁻ y, U i y)^youngFrameWeight s i ≤
      ∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i)
    (hs : 1<s) :
    c.toReal*(∏ i, (∫ y, (U i y).toReal)^youngFrameWeight s i) ≤
       ∫ z : YoungPair n, ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z)).toReal^youngFrameWeight s i := by
  let L := fun z : YoungPair n => ∏ i, (U i (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i
  have hL : Measurable L := Finset.measurable_prod _ (fun i _ =>
    ((hU i).comp (youngFrameMap _ s i).continuous.measurable).pow_const _)
  have hLfin : (∫⁻ z,L z) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.prod_ne_top
    (fun i _ => ENNReal.rpow_ne_top_of_nonneg (youngFrameWeight_nonneg hs.le i) (hfin i))) (young_frame_bound n s hs U hU)
  have hpt (z : YoungPair n) : ∏ i, (U i (youngFrameMap _ s i z)).toReal^youngFrameWeight s i = (L z).toReal := by
    simp only [L,ENNReal.toReal_prod,ENNReal.toReal_rpow]
  have hm i := integral_toReal (hU i).aemeasurable (ae_lt_top (hU i) (hfin i))
  simp_rw [hpt, hm]
  rw [integral_toReal hL.aemeasurable (ae_lt_top hL hLfin)]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_rpow] using ENNReal.toReal_mono hLfin hE

/-- A unit input within a relative deficit α of the diagonal Young bound lifts
to a real integrable geometric datum with ratio at least (1−α)^(1/s). -/
theorem frame_near_of_diagonal {n : ℕ} {s α : ℝ} (hs : 1<s) (hα : α<1) (F : Rn n → ℝ≥0)
    (hf : Measurable F) (hunit : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hNear : ENNReal.ofReal (1-α)*youngMomentConstant 1 n s ≤ cubeMoment 1 n s F) :
    let u := youngFirstDensity n s F
    ∃ v : YoungHilbert n → ℝ, Integrable u ∧ Integrable v ∧ (∀ y, 0≤u y) ∧ (∀ y, 0≤v y) ∧
      (∫ y, u y)=1 ∧ (0<∫ y, v y) ∧
      (1-α)^(1/s)*(∏ i, (∫ y, (![u,u,v] i) y)^youngFrameWeight s i) ≤
        ∫ z : YoungPair n, ∏ i, ((![u,u,v] i) (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i := by
  classical
  let μ := euclideanMeasure n
  let C := ENNReal.ofReal (diagonalYoungFactor s)^n
  let R := pairCorrelation μ (liftNN F) (liftNN F)
  let q := criticalExponent 1 s
  let a := youngFrameA s
  let b := youngFrameB s
  let w := (s+1)/(2*s)
  let v := (s-1)/s
  let H := fun x => R x^(s-1)
  let U₀ := fun y : YoungHilbert n => ((F (WithLp.ofLp y):ℝ≥0∞))^q
  let U₂ := fun y : YoungHilbert n => (R ((2*a) • WithLp.ofLp y))^s
  let U : Fin 3 → YoungHilbert n → ℝ≥0∞ := ![U₀,U₀,U₂]
  have hs0 := zero_lt_one.trans hs
  have hs1 := sub_pos.mpr hs
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have hv : 0<v := div_pos hs1 hs0
  have hqw : q*w=1 := by dsimp [q,criticalExponent,w]; norm_num; field_simp; ring
  have hsV : s*v=s-1 := by dsimp [v]; field_simp
  have hC : C≠0 := by dsimp [C,diagonalYoungFactor]; positivity
  have hCt : C≠⊤ := by dsimp [C]; finiteness
  have : SigmaFinite μ := by dsimp [μ,euclideanMeasure]; infer_instance
  have hf' : Measurable (liftNN F) := hf.coe_nnreal_ennreal
  have hR : Measurable R := Measurable.lintegral_prod_right
    ((hf'.comp measurable_snd).mul (hf'.comp (measurable_snd.add measurable_fst)))
  have hH : Measurable H := hR.pow_const _
  let J := ∫⁻ t, (R t)^s ∂μ
  have hJnear : ENNReal.ofReal (1-α)*C ≤ J := by
    rw [cubeMoment_one n s F hf.aemeasurable,youngMomentConstant_one] at hNear
    exact hNear
  have hJ : J≠0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr hα)).ne' hC)) hJnear).ne'
  have hJt : J≠⊤ := by
    have h := sharp_diagonal_young n s hs.le F hf
    have hq' : criticalExponent 1 s = 2*s/(s+1) := by simp [criticalExponent]; ring
    rw [hq'] at hunit
    change J ≤ C*_ at h
    rw [hunit,ENNReal.one_rpow,mul_one] at h
    exact ne_top_of_le_ne_top hCt h
  have he : MeasurePreserving (WithLp.ofLp : YoungHilbert n → Rn n) volume μ := PiLp.volume_preserving_ofLp (Fin n)
  have hpair : MeasurePreserving (fun z : YoungPair n => (WithLp.ofLp z.fst,WithLp.ofLp z.snd))
      volume (μ.prod μ) := (he.prod he).comp (WithLp.volume_preserving_ofLp (YoungHilbert n) (YoungHilbert n))
  have hU0 : Measurable U₀ := (hf'.comp he.measurable).pow_const q
  have hU2 : Measurable U₂ := (hR.comp (he.measurable.const_smul (2*a))).pow_const s
  have hU (i : Fin 3) : Measurable (U i) := by fin_cases i <;> first | exact hU0 | exact hU2
  have hm0 : (∫⁻ y, U₀ y) = 1 := (he.lintegral_comp (hf'.pow_const q)).trans hunit
  let D := youngDilation n (2*a)
  let k := youngDilation n b * D
  have hD : D≠0 := by dsimp [D,youngDilation]; positivity
  have hDt : D≠⊤ := ENNReal.ofReal_ne_top
  have hk : k≠0 := by dsimp [k,D,youngDilation]; positivity
  have hkt : k≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDt
  have hm2 : (∫⁻ y, U₂ y) = D*J := calc
    _ = ∫⁻ y, R ((2*a) • y)^s ∂μ := he.lintegral_comp ((hR.comp (measurable_const_smul _)).pow_const s)
    _ = _ := by rw [young_lintegral_smul n (by positivity : 0<2*a) (fun y => R y^s) (hR.pow_const s)]
  have hfin (i : Fin 3) : (∫⁻ y, U i y) ≠ ⊤ := by
    fin_cases i <;> first | exact hm0.trans_ne ENNReal.one_ne_top | exact hm2.trans_ne (ENNReal.mul_ne_top hDt hJt)
  let P := fun z : Rn n × Rn n => liftNN F ((-a)•z.1+b•z.2)*liftNN F (a•z.1+b•z.2)*H ((2*a)•z.1)
  have hP : Measurable P := by dsimp only [P]; fun_prop
  have hpoint (z : YoungPair n) : (∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i) =
      P (WithLp.ofLp z.fst,WithLp.ofLp z.snd) := by
    rw [Fin.prod_univ_three]
    change (_^q)^w * (_^q)^w * (R ((2*a) • WithLp.ofLp ((1:ℝ)• z.fst+(0:ℝ)•z.snd))^s)^v = _
    simp only [← ENNReal.rpow_mul,hqw,hsV,ENNReal.rpow_one,one_smul,zero_smul,add_zero]
    rfl
  have hpairing : (∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i) = k*J := by
    simp_rw [hpoint]
    rw [hpair.lintegral_comp hP, show (∫⁻ z, P z ∂μ.prod μ) = k * ∫⁻ t, R t*H t ∂μ from
      young_frame_change_variables n ha hb _ _ _ hf' hf' hH]
    apply congrArg (k*·)
    apply lintegral_congr; intro t
    calc
      _ = (R t)^1*(R t)^(s-1) := by rw [ENNReal.rpow_one]
      _ = (R t)^(1+(s-1)) := (ENNReal.rpow_add_of_nonneg _ _ zero_le_one hs1.le).symm
      _ = _ := by congr 1; ring
  let c := ENNReal.ofReal (1-α)^(1/s)
  have hE : c*(∏ i, (∫⁻ y, U i y)^youngFrameWeight s i) ≤
      ∫⁻ z : YoungPair n, ∏ i, (U i (youngFrameMap _ s i z))^youngFrameWeight s i := by
    rw [hpairing,Fin.prod_univ_three]
    change c*((∫⁻ y,U₀ y)^w*(∫⁻ y,U₀ y)^w*(∫⁻ y,U₂ y)^v) ≤ k*J
    rw [hm0,hm2,ENNReal.one_rpow,one_mul,one_mul,ENNReal.mul_rpow_of_nonneg _ _ hv.le]
    have hconst : k⁻¹*D^v=C^(1/s) := young_dilation_constant n s hs
    have hew : 1/s+v=1 := by dsimp [v]; field_simp; ring
    have hC' : k*C^(1/s)=D^v := by rw [← hconst,← mul_assoc, ENNReal.mul_inv_cancel hk hkt,one_mul]
    have hroot := ENNReal.rpow_le_rpow hJnear (one_div_pos.mpr hs0).le
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hs0).le] at hroot
    change c*C^(1/s) ≤ J^(1/s) at hroot
    calc
      _ = k*((c*C^(1/s))*J^v) := by rw [← hC']; ac_rfl
      _ ≤ k*(J^(1/s)*J^v) := by gcongr
      _ = _ := by rw [← ENNReal.rpow_add_of_nonneg _ _ (one_div_pos.mpr hs0).le hv.le,hew,ENNReal.rpow_one]
  let u := youngFirstDensity n s F
  let v' := fun y => (U₂ y).toReal
  have HU (y) : (U₀ y).toReal = u y := by simp [U₀,u,youngFirstDensity,q,← ENNReal.toReal_rpow]
  have hi := integrable_toReal_of_lintegral_ne_top hU0.aemeasurable (hfin 0)
  have hm := integral_toReal hU0.aemeasurable (ae_lt_top hU0 (hfin 0))
  simp_rw [HU] at hi hm
  refine ⟨v',hi,integrable_toReal_of_lintegral_ne_top hU2.aemeasurable (hfin 2),
    (fun y => Real.rpow_nonneg (F _).coe_nonneg _),fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · exact hm.trans (by rw [hm0, ENNReal.toReal_one])
  · change 0 < ∫ y, (U₂ y).toReal
    rw [integral_toReal hU2.aemeasurable (ae_lt_top hU2 (hfin 2)),hm2]
    exact ENNReal.toReal_pos (mul_ne_zero hD hJ) (ENNReal.mul_ne_top hDt hJt)
  · have hp (i : Fin 3) (y) : (U i y).toReal = (![u,u,v'] i) y := by
      fin_cases i <;> first | exact HU y | rfl
    have hc : c.toReal = (1-α)^(1/s) := by rw [show c = (ENNReal.ofReal (1-α))^(1/s) from rfl,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sub_nonneg.mpr hα.le)]
    simpa only [hp,hc] using frame_lower_toReal U hU hfin c hE hs

/-- A unit extremizer gives two real integrable densities (the first
occurs twice) extremising exactly the geometric Brascamp–Lieb datum. -/
theorem frame_extremal_of_diagonal {n : ℕ} {s : ℝ} (hs : 1<s) (F : Rn n → ℝ≥0)
    (hf : Measurable F) (hunit : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hExt : cubeMoment 1 n s F = youngMomentConstant 1 n s) :
    let u := youngFirstDensity n s F
    ∃ v : YoungHilbert n → ℝ, Integrable u ∧ Integrable v ∧ (∀ y, 0≤u y) ∧ (∀ y, 0≤v y) ∧
      (∫ y, u y)=1 ∧ (0<∫ y, v y) ∧
      (∫ z : YoungPair n, ∏ i, ((![u,u,v] i) (youngFrameMap (YoungHilbert n) s i z))^youngFrameWeight s i) =
        ∏ i, (∫ y, (![u,u,v] i) y)^youngFrameWeight s i := by
  obtain ⟨v,hu,hv,hu0,hv0,hum,hvm,hl⟩ := frame_near_of_diagonal (α:=0) hs (by norm_num) F hf hunit
    (by rw [hExt]; simp)
  refine ⟨v,hu,hv,hu0,hv0,hum,hvm,le_antisymm ?_ (by simpa using hl)⟩
  let V := YoungHilbert n
  let D : GeometricBrascampLieb.Datum (Fin 3) (YoungPair n) (fun _ => V) :=
    .ofNormSq (youngFrameMap V s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry V (zero_lt_one.trans hs)) (youngFrameMap_resolution V (zero_lt_one.trans hs))
  let f : Fin 3 → V → ℝ := ![youngFirstDensity n s F,youngFirstDensity n s F,v]
  have hi (i : Fin 3) : Integrable (f i) := by fin_cases i <;> first | exact hu | exact hv
  have hn (i : Fin 3) : ∀ x, 0≤ f i x := by fin_cases i <;> first | exact hu0 | exact hv0
  exact D.integral_prod_le_integrable hi hn

/-- For a completed-measurable normalized exact Young extremizer, its density
agrees almost everywhere with a real unit density whose heat score is affine
at every positive time. -/
theorem affine_score_of_diagonal_extremal {n : ℕ} {s : ℝ} (hs : 1<s)
    (F : Rn n → ℝ≥0) (hf : AEMeasurable F (euclideanMeasure n))
    (hunit : (∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1)
    (hExt : youngMomentConstant 1 n s ≤ cubeMoment 1 n s F) :
    ∃ u : YoungHilbert n → ℝ, u =ᵐ[volume] youngFirstDensity n s F ∧
      ∃ (hu : Integrable u) (hu0 : ∀ y, 0≤u y) (hm : (∫ y,u y)=1),
        ∀ t : ℝ, 0<t →
          let W := GeometricBrascampLieb.convolutionLogHeatFlow hu hu0 (show 0 < (∫ y,u y) by rw [hm]; norm_num)
          ∃ L : YoungHilbert n →L[ℝ] YoungHilbert n, ∀ x, W.gradient t x = L x + W.gradient t 0 := by
  let μ := euclideanMeasure n
  let F' := hf.mk F
  have hEq : F =ᵐ[μ] F' := hf.ae_eq_mk
  have he : MeasurePreserving (WithLp.ofLp : YoungHilbert n → Rn n) volume μ :=
    PiLp.volume_preserving_ofLp (Fin n)
  have hunit' : (∫⁻ x, (F' x : ℝ≥0∞)^criticalExponent 1 s ∂μ) = 1 := by
    apply Eq.trans _ hunit
    apply lintegral_congr_ae; filter_upwards [hEq] with x hx; rw [hx]
  have hExt' : cubeMoment 1 n s F' = youngMomentConstant 1 n s := by
    apply le_antisymm
    · rw [cubeMoment_one n s F' hf.measurable_mk.aemeasurable, youngMomentConstant_one]
      have h := sharp_diagonal_young n s hs.le F' hf.measurable_mk
      have hq : criticalExponent 1 s = 2*s/(s+1) := by simp [criticalExponent]; ring
      rw [hq] at hunit'
      simpa only [μ, hunit', ENNReal.one_rpow,mul_one] using h
    · apply hExt.trans_eq
      unfold cubeMoment
      have : μ.IsAddLeftInvariant := by dsimp [μ,euclideanMeasure]; infer_instance
      rw [autocorrelation_congr_ae μ hEq]
  obtain ⟨v,hu,hv,hu0,hv0,hum,hvm,hE⟩ := frame_extremal_of_diagonal hs F' hf.measurable_mk hunit' hExt'
  refine ⟨youngFirstDensity n s F', ?_,hu,hu0,hum,?_⟩
  · have h := he.quasiMeasurePreserving.ae_eq_comp hEq
    filter_upwards [h] with y hy
    simp only [Function.comp_apply] at hy
    simp only [youngFirstDensity, hy]
  · intro t ht
    exact affine_heat_score_of_young_frame_extremal hs _ v hu hv hu0 hv0 (hum ▸ zero_lt_one)
      hvm hE ht

end LpGowers
