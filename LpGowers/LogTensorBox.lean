module

public import LpGowers.LogMoments
public import LpGowers.ExtendedThreeMoments
public import LpGowers.CylinderBox

/-! # A product box for a normalized near-extremal autocorrelation

The first chain of section 6 gives three almost-unit moments of `R_d f`
and near-equality in symmetric degree lowering. Theorem 1.4(b) supplies
the same one-dimensional factors as functional Loomis–Whitney stability.
The arbitrary-set slicing step in Lemma 6.1 converts their product into
a product of measurable sets. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal symmDiff
namespace LpGowers

private theorem power_gap {a : ℝ} (ha : 0<a) (ha1 : a≤1) (x y : ℝ≥0∞) :
    (x^a-y^a)+(y^a-x^a) ≤ ((x-y)+(y-x))^a := by
  have directed (s t : ℝ≥0∞) : s^a-t^a ≤ (s-t)^a := by
    apply tsub_le_iff_left.mpr
    exact (ENNReal.rpow_le_rpow (show s ≤ t+(s-t) from le_add_tsub) ha.le).trans
      (ENNReal.rpow_add_le_add_rpow _ _ ha.le ha1)
  rcases le_total x y with h | h
  · simpa only [tsub_eq_zero_of_le h,tsub_eq_zero_of_le (ENNReal.rpow_le_rpow h ha.le),
      zero_add] using directed y x
  · simpa only [tsub_eq_zero_of_le h,tsub_eq_zero_of_le (ENNReal.rpow_le_rpow h ha.le),
      add_zero] using directed x y

private theorem density_power_to_indicator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (S : Set X) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    l1DensityError μ (fun x => (F x)^a) (S.indicator 1) ≤
      ∫⁻ x, ((F x-S.indicator 1 x)+(S.indicator 1 x-F x))^a ∂μ := by
  apply lintegral_mono
  intro x
  have h := power_gap ha ha1 (F x) (S.indicator 1 x)
  have he : (S.indicator (1 : X → ℝ≥0∞) x)^a = S.indicator 1 x := by
    by_cases hx : x ∈ S <;> simp [hx,ENNReal.zero_rpow_of_pos ha]
  rwa [he] at h

private theorem unit_tensor_scale_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → ℝ≥0∞) (hT : Measurable T) (ht : ∀x,T x ≠ ⊤) (h1 : (∫⁻ x, T x ∂μ)=1)
    {m : ℝ≥0∞} (hm : m≤1) : l1DensityError μ T (fun x => m*T x) = 1-m := by
  have he (x) : (T x-m*T x)+(m*T x-T x) = (1-m)*T x := by
    rw [tsub_eq_zero_of_le (mul_le_of_le_one_left' hm),add_zero,
      ENNReal.sub_mul (fun _ _ => ht x),one_mul]
  simp only [l1DensityError, he,lintegral_const_mul _ hT,h1,mul_one]

/-- A common measurable support for three near-unit moments, with a
measurable product box nearby in absolute Haar symmetric difference. -/
theorem normalized_log_support.{u} (j : ℕ) (κ : ℝ) (hκ : 0<κ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G]
      [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → ℝ≥0),
      AEMeasurable f μ → ordinaryGowers μ (j+1) f = 1 → ordinaryGowers μ (j+2+1) f = 1 →
      ENNReal.ofReal (1-δ) ≤ ordinaryGowers μ (j+2) f →
      ∃ (S : Set (Fin (j+2) → G)) (A : Fin (j+2) → Set G),
        let ν := cubeMeasure μ (j+2)
        let R := autocorrelation μ (j+2) f
        MeasurableSet S ∧ ν S ≠ ⊤ ∧ |ν.real S-1|≤κ ∧
        (∀ i, MeasurableSet (A i) ∧ μ (A i)≠0 ∧ μ (A i)≠⊤) ∧
        ν.real (S ∆ Set.univ.pi A) ≤ κ ∧
        ∀ t ∈ Set.Icc (logLowerPower (j+2)) 2,
          (∫⁻ x, ((R x - S.indicator 1 x)+(S.indicator 1 x - R x))^t ∂ν) ≤ ENNReal.ofReal κ := by
  let D := j+2
  let a := logLowerPower D
  let w := fun _ : Fin (j+2) => 1/((j:ℝ)+2)
  obtain ⟨hpar,hfor,ha1⟩ := logLower_parameters j
  have ha : 0<a := hfor.1
  obtain ⟨b,hb,hbox⟩ := box_of_uniform_tensor.{u} (j+1) (η:=κ/2) (by positivity)
  let τ := min (min κ (b/12)) (1/24)
  have hτ : 0<τ := lt_min (lt_min hκ (by positivity)) (by norm_num)
  have hτκ : τ≤κ := (min_le_left ..).trans (min_le_left ..)
  have hτb : τ≤b/12 := (min_le_left ..).trans (min_le_right ..)
  have hτsmall : τ≤1/24 := min_le_right ..
  obtain ⟨α,hα,hrig⟩ := three_moments_near_ennreal.{u} ha ha1 (show (1:ℝ)<2 by norm_num) hτ
  obtain ⟨β,hβ,hstab⟩ := degree_stability.{u} (j+1) (by omega) a (fun _ => 1) w hpar ha1.ne τ hτ
  let ε := min (β/2) (1/2)
  have hε : 0<ε := lt_min (half_pos hβ) (by norm_num)
  have hεβ : ε<β := lt_of_le_of_lt (min_le_left ..) (half_lt_self hβ)
  let ξ := min τ (min α ε)
  have hξ : 0<ξ := lt_min hτ (lt_min hα hε)
  have hξτ : ξ≤τ := min_le_left ..
  have hξα : ξ≤α := (min_le_right ..).trans (min_le_left ..)
  have hξε : ξ≤ε := (min_le_right ..).trans (min_le_right ..)
  have hξ1 : ξ<1 := by linarith
  obtain ⟨δ,hδ,hδ1,H⟩ := normalized_upper_moments.{u} j ξ hξ
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ f hf hlow hhigh hmid
  let ν := cubeMeasure μ D
  let R := autocorrelation μ D f
  let U := gowers μ D a f
  let m := ∫⁻ x, (R x)^a ∂ν
  have hR : Measurable R := measurable_autocorrelation_of_aemeasurable μ D hf
  obtain ⟨hU,hmom⟩ := H G μ f hf hlow hhigh hmid
  have hmass := hmom a (by simp [a,D])
  obtain ⟨S,hS,hSfin,hSvol,hSerr⟩ := hrig _ ν R hR
    (fun t ht => ⟨(ENNReal.ofReal_le_ofReal (sub_le_sub_left hξα 1)).trans (hmom t ht).1,(hmom t ht).2⟩)
  have hP : lowerProduct μ (j+1) (fun _ => 1) w f = 1 := by
    change gowers μ (j+1) 1 f = 1 at hlow
    simp [lowerProduct,hlow]
  have hx : 0 < ENNReal.ofReal (1-ξ) := ENNReal.ofReal_pos.mpr (sub_pos.mpr hξ1)
  have hnear : ENNReal.ofReal (1-ε)*lowerProduct μ (j+1) (fun _ => 1) w f ≤ U := by
    rw [hP,mul_one]
    exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left hξε 1)).trans hU.1
  have hlower (i : Fin (j+2)) : 0<gowers μ (j+1) (1:ℝ) f ∧ gowers μ (j+1) 1 f < ⊤ := by
    change gowers μ (j+1) 1 f = 1 at hlow
    simp [hlow]
  obtain ⟨r,hr,hjoint,_⟩ := hstab ε hε hεβ G μ f hf (hx.trans_le hU.1)
    (hU.2.trans_lt ENNReal.one_lt_top) hlower (Or.inl ⟨hfor,hnear⟩)
  let T := fun x : Fin D → G => ∏ i, (r i (x i):ℝ≥0∞)
  have hT : Measurable T := Finset.measurable_prod _ fun i _ => (hr i).1.coe_nnreal_ennreal.comp (measurable_pi_apply i)
  have hT1 : (∫⁻ x, T x ∂ν)=1 := by
    rw [show (∫⁻ x, T x ∂ν) = ∏ i, ∫⁻ y, (r i y:ℝ≥0∞) ∂μ from
      lintegral_pi_separated μ D _ (fun i => (hr i).1.coe_nnreal_ennreal)]
    simp only [fun i => (hr i).2,Finset.prod_const_one]
  have hTfin x : T x ≠ ⊤ := ENNReal.prod_ne_top (fun i _ => ENNReal.coe_ne_top)
  have ht1 : m≤1 := hmass.2
  have ht0 : ENNReal.ofReal (1-ξ)≤m := hmass.1
  have hsub : 1-m ≤ ENNReal.ofReal τ := by
    apply tsub_le_iff_left.mpr
    have hsum : (1:ℝ≥0∞)=ENNReal.ofReal (1-ξ)+ENNReal.ofReal ξ := by
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hξ1.le) hξ.le,sub_add_cancel,ENNReal.ofReal_one]
    rw [hsum]
    exact add_le_add ht0 (ENNReal.ofReal_le_ofReal hξτ)
  have hTscale := (unit_tensor_scale_error ν T hT hTfin hT1 ht1).le.trans hsub
  have hN : (lp ν a R)^a=m := by simp [lp,m,← ENNReal.rpow_mul,ha.ne']
  change l1DensityError ν (fun x => R x^a) (fun x => (lp ν a R)^a*T x) ≤ _ at hjoint
  rw [hN] at hjoint
  have hscaleF : l1DensityError ν (fun x => m*T x) (fun x => R x^a) ≤ ENNReal.ofReal τ := by
    rw [l1DensityError_comm]
    exact hjoint.trans (mul_le_of_le_one_right' ht1)
  have hFset : l1DensityError ν (fun x => R x^a) (S.indicator 1) ≤ ENNReal.ofReal τ :=
    (density_power_to_indicator ν R S ha ha1.le).trans (hSerr a ⟨le_rfl,by linarith⟩)
  have herr : l1DensityError ν T (S.indicator 1) ≤ 3*ENNReal.ofReal τ := by
    have hmT : Measurable (fun x => m*T x) := hT.const_mul m
    have hRa := hR.pow_const a
    have hSi : Measurable (S.indicator (1 : (Fin D → G) → ℝ≥0∞)) := measurable_const.indicator hS
    refine (l1DensityError_triangle ν hT hmT hSi).trans ((add_le_add hTscale
      ((l1DensityError_triangle ν hmT hRa hSi).trans (add_le_add hscaleF hFset))).trans_eq ?_)
    ring
  have hsmall : 3*ENNReal.ofReal τ < 1 := by
    rw [← ENNReal.ofReal_ofNat 3,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨hS0,_,he⟩ := normalize_indicator_fibre ν hS hT hT1 (b:=1) one_ne_zero ENNReal.one_ne_top hsmall herr
  have he' : l1DensityError ν (S.indicator (fun _ => (ν S)⁻¹)) T ≤ ENNReal.ofReal b := by
    rw [l1DensityError_comm]
    refine he.trans ?_
    rw [← mul_assoc,show (3:ℝ≥0∞)*3=9 by norm_num,← ENNReal.ofReal_ofNat 9,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤9)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨A,hA,hDiff⟩ := hbox μ S hS hS0 hSfin (fun i x => ↑(r i x))
    (fun i => (hr i).1.coe_nnreal_ennreal) (fun i => (hr i).2) he'
  have hsv : ν.real S ≤ 2 := by linarith only [(abs_le.mp hSvol).2,hτsmall]
  have hbound : κ/2*ν.real S ≤ κ := by nlinarith only [mul_le_mul_of_nonneg_left hsv hκ.le]
  exact ⟨S,A,hS,hSfin,hSvol.trans hτκ,hA,hDiff.trans hbound,
    fun t ht => (hSerr t ht).trans (ENNReal.ofReal_le_ofReal hτκ)⟩

end LpGowers
