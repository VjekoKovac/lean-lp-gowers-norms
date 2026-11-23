module

public import LpGowers.InverseYoung
public import LpGowers.ExtendedHolder
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Flatness at a nearly extremal Young fiber

In the proof of Eisner–Tao's inverse Young inequality, Hölder stability aligns
two densities and their normalized product. The threshold below converts those
two alignments to closeness to a constant on a measurable set. -/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace LpGowers

private theorem plateau_error {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    |x - (if c/2 < x then c else 0)| ≤ 2*|x-y| + 4*|y-x*y/c| := by
  have hfac : y-x*y/c = (y/c)*(c-x) := by field_simp
  rw [hfac,abs_mul,abs_of_nonneg (div_nonneg hy hc.le),abs_sub_comm c x]
  by_cases hx0 : c/2 < x
  · rw [ite_eq_left hx0]
    by_cases hxy : x/2 ≤ y
    · have hv : 1 ≤ 4*(y/c) := by rw [← mul_div_assoc, le_div_iff₀ hc]; linarith
      nlinarith only [mul_le_mul_of_nonneg_right hv (abs_nonneg (x-c)),abs_nonneg (x-y)]
    · rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      have ha : |x-c| ≤ x := abs_le.mpr (by constructor <;> linarith)
      nlinarith only [ha,lt_of_not_ge hxy,mul_nonneg (div_nonneg hy hc.le) (abs_nonneg (x-c))]
  · rw [ite_eq_right hx0,sub_zero,abs_of_nonneg hx,abs_of_nonpos (by linarith : x-c ≤ 0),neg_sub]
    by_cases hxy : x/2 ≤ y
    · have hv : c/2 ≤ c-x := by linarith
      have hm := mul_le_mul_of_nonneg_left hv (div_nonneg hy hc.le)
      rw [show y/c*(c/2) = y/2 by field_simp] at hm
      linarith [abs_nonneg (x-y)]
    · rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      nlinarith only [lt_of_not_ge hxy,mul_nonneg (div_nonneg hy hc.le) (by linarith : 0 ≤ c-x)]

/-- The L¹ gap of two finite nonnegative functions is the two-sided
truncated difference used in the product stability theorem. -/
theorem lpDist_one_eq_densityError {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (u v : X → ℝ≥0) : lpDist ν 1 u v = l1DensityError ν (liftNN u) (liftNN v) := by
  simp only [lpDist,lp,div_one,ENNReal.rpow_one,l1DensityError,liftNN]
  apply lintegral_congr
  intro x
  rw [edist_nndist, NNReal.nndist_eq]
  rw [← ENNReal.coe_sub,← ENNReal.coe_sub,← ENNReal.coe_add]
  apply congrArg (fun t : ℝ≥0 => (t:ℝ≥0∞))
  rcases le_total (u x) (v x) with h | h
  · simp [tsub_eq_zero_of_le h]
  · simp [tsub_eq_zero_of_le h]

/-- Thresholding the first density at half the plateau height. The bound
is uniform in that height, so it survives changes of Haar normalization. -/
theorem plateau_of_product_alignment {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {u v : X → ℝ≥0} (hu : AEMeasurable u ν) (hv : AEMeasurable v ν) {c : ℝ≥0} (hc : 0 < c) :
    let w := fun x => u x * v x / c
    let E := {x | c/2 < u x}
    lpDist ν 1 u (E.indicator (fun _ => c)) ≤ 2 * lpDist ν 1 u v + 4 * lpDist ν 1 v w := by
  classical
  intro w E
  have hw : AEMeasurable w ν := (hu.mul hv).div_const _
  have hpoint (x) : edist (u x) (E.indicator (fun _ => c) x) ≤
      2 * edist (u x) (v x) + 4 * edist (v x) (w x) := by
    simp only [edist_dist,NNReal.dist_eq]
    have h := plateau_error (x := (u x : ℝ)) (y := (v x : ℝ)) (u x).coe_nonneg (v x).coe_nonneg (show 0 < (c:ℝ) from hc)
    have hcast : (↑(E.indicator (fun _ => c) x):ℝ) = if (c:ℝ)/2 < u x then (c:ℝ) else 0 := by
      by_cases h' : c/2 < u x
      · have he : x ∈ E := h'
        simp [he, show (c:ℝ)/2 < u x by exact_mod_cast h']
      · have he : x ∉ E := h'
        simp [he, show ¬ (c:ℝ)/2 < u x by exact_mod_cast h']
    rw [hcast]
    have hh := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (abs_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _)), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)] at hh
    simp only [w, NNReal.coe_div, NNReal.coe_mul]
    simpa only [ENNReal.ofReal_ofNat] using hh
  simp only [lpDist,lp,div_one,ENNReal.rpow_one]
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_add_left' ((hu.edist hv).const_mul _),
    lintegral_const_mul'' _ (hu.edist hv),lintegral_const_mul'' _ (hv.edist hw)]

private def youngWeights (t : ℝ) : Fin 3 → ℝ := ![(1-t)/2,(1-t)/2,t]

private theorem youngWeights_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ i, 0 < youngWeights t i := by
  intro i; fin_cases i <;> simp [youngWeights] <;> linarith

private theorem youngWeights_sum (t : ℝ) : ∑ i, youngWeights t i = 1 := by
  simp [youngWeights,Fin.sum_univ_three]

private def youngDensities {X : Type*} (u v : X → ℝ≥0) (c : ℝ≥0) : Fin 3 → X → ℝ≥0 :=
  ![u,v,fun x => u x*v x/c]

private theorem young_factors {X : Type*} (u v : X → ℝ≥0) (c : ℝ≥0) (hc : 0<c)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : X) :
    ((u x * v x : ℝ≥0) ^ ((1+t)/2) : ℝ≥0) =
      c^t * ∏ i, (youngDensities u v c i x)^(youngWeights t i) := by
  simp only [youngWeights,youngDensities,Fin.prod_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons, NNReal.div_rpow,
    NNReal.mul_rpow]
  have h : (1-t)/2+t = (1+t)/2 := by ring
  rw [← h, NNReal.rpow_add_of_nonneg _ (by linarith : (0:ℝ) ≤ (1-t)/2) ht.le,
    NNReal.rpow_add_of_nonneg _ (by linarith : (0:ℝ) ≤ (1-t)/2) ht.le]
  field_simp [(NNReal.rpow_pos (p:=t) hc).ne']

/-- Three-factor Hölder stability at a fixed shift forces closeness to a
plateau. Here `t` is the reciprocal of the Young output exponent, and the
height `c` is the integral of the product of the two unit-mass densities. -/
theorem young_fiber_plateau.{u} {t η : ℝ} (ht : 0<t) (ht1 : t<1) (hη : 0<η) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ (X : Type u) [MeasurableSpace X] (ν : Measure X)
      (u v : X → ℝ≥0) (c : ℝ≥0), 0 < c → AEMeasurable u ν → AEMeasurable v ν →
      (∫⁻ x, (u x : ℝ≥0∞) ∂ν) = 1 → (∫⁻ x, (v x : ℝ≥0∞) ∂ν) = 1 →
      (∫⁻ x, (u x : ℝ≥0∞) * v x ∂ν) = c →
      ENNReal.ofReal (1-β)*(c:ℝ≥0∞)^t ≤ ∫⁻ x, (↑(u x*v x) : ℝ≥0∞)^((1+t)/2) ∂ν →
      lpDist ν 1 u ({x | c/2 < u x}.indicator (fun _ => c)) ≤ ENNReal.ofReal η := by
  obtain ⟨δ,hδ,hst⟩ := holder_stability_ennreal (youngWeights t) (youngWeights_pos ht ht1)
    (youngWeights_sum t) (show 0<η/6 by positivity)
  let β := min (δ/2) (1/2)
  have hβ : 0<β := lt_min (half_pos hδ) (by norm_num)
  have hβ1 : β<1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hβd : β<δ := lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)
  refine ⟨β,hβ,hβ1,?_⟩
  intro X _ ν u v c hc hu hv hIu hIv hP hnear
  let w := fun x => u x*v x/c
  let T := fun i => liftNN (youngDensities u v c i)
  let g := fun x => ∏ i, T i x ^ youngWeights t i
  have hI (i) : AEMeasurable (T i) ν := by
    fin_cases i
    · exact hu.coe_nnreal_ennreal
    · exact hv.coe_nnreal_ennreal
    · exact ((hu.mul hv).div_const c).coe_nnreal_ennreal
  have hwI : (∫⁻ x, (w x:ℝ≥0∞) ∂ν) = 1 := by
    simp only [w, div_eq_mul_inv, ENNReal.coe_mul, ENNReal.coe_inv hc.ne']
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hc.ne')),hP,
      ENNReal.mul_inv_cancel (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
  have hIn (i) : (∫⁻ x, T i x ∂ν) ≤ 1 := by
    fin_cases i
    · exact hIu.le
    · exact hIv.le
    · exact hwI.le
  have hrewrite (x) : (↑(u x*v x) : ℝ≥0∞)^((1+t)/2) = (c:ℝ≥0∞)^t*g x := by
    have hcast := congrArg (fun z : ℝ≥0 => (z:ℝ≥0∞)) (young_factors u v c hc ht ht1 x)
    simpa only [g,T,liftNN,ENNReal.coe_mul, Fin.prod_univ_three, ENNReal.coe_rpow_of_nonneg
      _ (by linarith : 0 ≤ (1+t)/2), ENNReal.coe_rpow_of_nonneg _ ht.le,
      ENNReal.coe_rpow_of_nonneg _ (youngWeights_pos ht ht1 _).le] using hcast
  simp_rw [hrewrite] at hnear
  have hmeas : AEMeasurable g ν :=
    Finset.aemeasurable_fun_prod _ (fun i _ => (hI i).pow_const _)
  rw [lintegral_const_mul'' _ hmeas, mul_comm (ENNReal.ofReal _)] at hnear
  have hz : (c:ℝ≥0∞)^t ≠ 0 := (ENNReal.rpow_pos (by exact_mod_cast hc) ENNReal.coe_ne_top).ne'
  have ht0 : (c:ℝ≥0∞)^t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht.le ENNReal.coe_ne_top
  have hbound := hst β hβ.le hβd ν T hI hIn ((ENNReal.mul_le_mul_iff_right hz ht0).mp hnear)
  have h1 : lpDist ν 1 u v ≤ ENNReal.ofReal (η/6) := by
    rw [lpDist_one_eq_densityError]; exact (hbound 0).2 1
  have h2 : lpDist ν 1 v w ≤ ENNReal.ofReal (η/6) := by
    rw [lpDist_one_eq_densityError]; exact (hbound 1).2 2
  have hgoal := plateau_of_product_alignment ν hu hv hc
  refine hgoal.trans ((add_le_add (mul_le_mul le_rfl h1 zero_le zero_le)
     (mul_le_mul le_rfl h2 zero_le zero_le)).trans_eq ?_)
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring


/-- Interpolating the two unit-mass densities with their product bounds
the Young correlation at every shift by the appropriate power of the
density correlation. -/
theorem young_fiber_bound {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {u v : X → ℝ≥0} (hu : AEMeasurable u ν) (hv : AEMeasurable v ν)
    (hIu : (∫⁻ x, (u x : ℝ≥0∞) ∂ν) = 1) (hIv : (∫⁻ x, (v x : ℝ≥0∞) ∂ν) = 1)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    (∫⁻ x, (↑(u x*v x) : ℝ≥0∞)^((1+t)/2) ∂ν) ≤ (∫⁻ x, (u x : ℝ≥0∞)*v x ∂ν)^t := by
  let T := fun i => liftNN (youngDensities u v 1 i)
  have hI (i) : AEMeasurable (T i) ν := by
    fin_cases i
    · exact hu.coe_nnreal_ennreal
    · exact hv.coe_nnreal_ennreal
    · exact ((hu.mul hv).div_const 1).coe_nnreal_ennreal
  have h := ENNReal.lintegral_prod_norm_pow_le (μ:=ν) Finset.univ (fun i _ => hI i)
    (youngWeights_sum t) (fun i _ => (youngWeights_pos ht ht1 i).le)
  have hrewrite (x) : (↑(u x*v x) : ℝ≥0∞)^((1+t)/2) = ∏ i, T i x ^ youngWeights t i := by
    have hcast := congrArg (fun z : ℝ≥0 => (z:ℝ≥0∞)) (young_factors u v 1 one_pos ht ht1 x)
    simpa only [T,liftNN,ENNReal.coe_mul,Fin.prod_univ_three, NNReal.one_rpow,one_mul,
      ENNReal.coe_rpow_of_nonneg _ (by linarith : 0 ≤ (1+t)/2),
      ENNReal.coe_rpow_of_nonneg _ (youngWeights_pos ht ht1 _).le] using hcast
  simp_rw [hrewrite]
  simpa only [Fin.prod_univ_three,youngWeights,T,youngDensities,liftNN,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,div_one,
    ENNReal.coe_mul,hIu,hIv,ENNReal.one_rpow,one_mul] using h

private theorem exists_positive_good_fiber {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {M I : X → ℝ≥0∞} (hM : Measurable M) (hMI : (∫⁻ a, M a ∂ν) = 1) (hI : ∀ a, I a ≤ M a)
    {b : ℝ≥0∞} (hb : b < ∫⁻ a, I a ∂ν) :
    ∃ a, M a ≠ 0 ∧ M a ≠ ⊤ ∧ b * M a ≤ I a := by
  by_contra! hn
  have hae := ae_lt_top' hM.aemeasurable (hMI ▸ ENNReal.one_ne_top)
  have hle : ∀ᵐ a ∂ν, I a ≤ b*M a := by
    filter_upwards [hae] with a ha
    by_cases hzero : M a = 0
    · simpa only [hzero,mul_zero] using hI a
    · exact (hn a hzero ha.ne).le
  have hle' := lintegral_mono_ae hle
  rw [lintegral_const_mul _ hM,hMI,mul_one] at hle'
  exact hb.not_ge hle'

/-- A nearly maximal integral of identical-input Young correlations has a
positive finite fiber near the pointwise Hölder bound. Thresholding its
density gives an approximate plateau for the original input. -/
theorem exists_young_plateau.{u} (d : ℕ) (hd : 2≤d) (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (G : Type u) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
        (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] (f : G → ℝ≥0), Measurable f →
      let s := 2*(d:ℝ)/(d+1)
      (∫⁻ x, (f x : ℝ≥0∞)^s ∂μ) = 1 →
      ENNReal.ofReal (1-δ) ≤ ∫⁻ a, (∫⁻ x, (f x : ℝ≥0∞)*f (x+a) ∂μ)^(d:ℝ) ∂μ →
      ∃ (E : Set G) (c : ℝ≥0), MeasurableSet E ∧ 0<c ∧
        lpDist μ 1 (fun x => f x ^ s) (E.indicator (fun _ => c)) ≤ ENNReal.ofReal η := by
  have hD : (1:ℝ) < d := by exact_mod_cast (by omega : 1<d)
  have hD0 : (0:ℝ) < d := by linarith
  let t := 1/(d:ℝ)
  let s := 2*(d:ℝ)/(d+1)
  have ht : 0<t := one_div_pos.mpr hD0
  have ht1 : t<1 := (div_lt_one hD0).mpr hD
  have hs : 0<s := by dsimp [s]; positivity
  have htd : t*(d:ℝ)=1 := one_div_mul_cancel hD0.ne'
  have hsj : s*((1+t)/2)=1 := by dsimp [s,t]; field_simp
  obtain ⟨β,hβ,hβ1,hplateau⟩ := young_fiber_plateau.{u} ht ht1 hη
  let b := (1-β)^(d:ℝ)
  let δ := (1-b)/2
  have hb : 0<b := Real.rpow_pos_of_pos (sub_pos.mpr hβ1) _
  have hb1 : b<1 := Real.rpow_lt_one (sub_nonneg.mpr hβ1.le) (by linarith) hD0
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hδ1 : δ<1 := by dsimp [δ]; linarith
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ μ _ _ f hf _ hFm hR
  let F := fun x => f x ^ s
  have hF : Measurable F := hf.pow_const s
  have hFI : (∫⁻ x, (F x : ℝ≥0∞) ∂μ)=1 := by
    simpa only [F,ENNReal.coe_rpow_of_nonneg _ hs.le] using hFm
  let M := fun a => ∫⁻ x, (F x : ℝ≥0∞)*F (x+a) ∂μ
  let R := fun a => ∫⁻ x, (f x : ℝ≥0∞)*f (x+a) ∂μ
  have hM : Measurable M := Measurable.lintegral_prod_right
    ((hF.coe_nnreal_ennreal.comp measurable_snd).mul
      (hF.coe_nnreal_ennreal.comp (measurable_snd.add measurable_fst)))
  have hMI : (∫⁻ a, M a ∂μ)=1 := by
    dsimp only [M]
    rw [lintegral_lintegral_swap (μ:=μ) (ν:=μ)]
    · have heq (x) : (∫⁻ a, (F x : ℝ≥0∞)*F (x+a) ∂μ) = F x := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          lintegral_add_left_eq_self (fun y => (F y : ℝ≥0∞)),hFI,mul_one]
      simpa only [heq] using hFI
    · exact ((hF.coe_nnreal_ennreal.comp measurable_snd).mul
        (hF.coe_nnreal_ennreal.comp (measurable_snd.add measurable_fst))).aemeasurable
  have htrans (a : G) : (∫⁻ x, (F (x+a) : ℝ≥0∞) ∂μ)=1 :=
    (lintegral_add_right_eq_self (fun y => (F y:ℝ≥0∞)) a).trans hFI
  have hRrepr (a : G) : (∫⁻ x, (↑(F x*F (x+a)):ℝ≥0∞)^((1+t)/2) ∂μ) = R a := by
    apply lintegral_congr
    intro x
    simp only [F,ENNReal.coe_mul,ENNReal.coe_rpow_of_nonneg _ hs.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0≤(1+t)/2),← ENNReal.rpow_mul, hsj,
      ENNReal.rpow_one]
  have hpoint (a : G) : R a ^ (d:ℝ) ≤ M a := by
    have h := young_fiber_bound μ hF.aemeasurable (hF.comp (measurable_add_const a)).aemeasurable
      hFI (htrans a) ht ht1
    simp only [Function.comp_apply] at h
    rw [hRrepr a] at h
    simpa only [← ENNReal.rpow_mul, htd, ENNReal.rpow_one, M] using ENNReal.rpow_le_rpow h hD0.le
  have hlow : ENNReal.ofReal b < ∫⁻ a, R a^(d:ℝ) ∂μ := by
    refine lt_of_lt_of_le ?_ hR
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
    dsimp [δ]; linarith
  obtain ⟨a,h0,hfin,hnear⟩ := exists_positive_good_fiber μ hM hMI hpoint hlow
  let c := (M a).toNNReal
  have hc_eq : (c:ℝ≥0∞) = M a := ENNReal.coe_toNNReal hfin
  have hc : 0<c := ENNReal.toNNReal_pos h0 hfin
  have hnear' : ENNReal.ofReal (1-β)*(c:ℝ≥0∞)^t ≤ R a := by
    apply (ENNReal.rpow_le_rpow_iff hD0).mp
    rw [ENNReal.mul_rpow_of_nonneg _ _ hD0.le,← ENNReal.rpow_mul, htd,ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hβ1.le) hD0.le,hc_eq]
    exact hnear
  refine ⟨{x | c/2 < F x},c,measurableSet_lt measurable_const hF,hc,?_⟩
  exact hplateau _ μ F (fun x => F (x+a)) c hc hF.aemeasurable
    (hF.comp (measurable_add_const a)).aemeasurable hFI (htrans a) hc_eq.symm
    ((hRrepr a).symm ▸ hnear')

end LpGowers
