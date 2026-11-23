module

public import LpGowers.SmallLeakage
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Tactic

/-! # Inverse Young inequality for indicators

A near-maximal autocorrelation moment forces a measurable set to be close
in symmetric difference to a coset of a compact open subgroup. The proof
uses additive overlaps, the compact approximation property of Haar measure,
and Eisner–Tao's small-difference lemma.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise symmDiff
namespace LpGowers
universe u

variable {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]

private def ov (E : Set G) (t : G) := μ.real (E ∩ (fun z => z+t) ⁻¹' E)

omit [T2Space G] in
private theorem measurable_ov {E : Set G} (hE : MeasurableSet E) :
    Measurable (ov μ E) :=
  (measurable_measure_prodMk_left (ν := μ)
    ((measurable_snd hE).inter ((measurable_snd.add measurable_fst) hE))).ennreal_toReal

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem ov_diff {E : Set G} (hE : MeasurableSet E) (hf : μ E ≠ ⊤) (u v : G) :
    ov μ E u + ov μ E v - μ.real E ≤ ov μ E (u-v) := by
  let T := fun (a : G) (S : Set G) => (fun z => z+a) ⁻¹' S
  have hT (a : G) (S : Set G) : μ.real (T a S) = μ.real S := by
    simp only [measureReal_def,T,measure_preimage_add_right]
  let X := E ∩ T u E
  let Y := E ∩ T v E
  have hu : μ.real (X ∪ Y) ≤ μ.real E :=
    measureReal_mono (union_subset inter_subset_left inter_subset_left) hf
  have hxy := measureReal_union_add_inter (μ := μ) (s := X) (t := Y)
    (hE.inter ((measurable_id.add_const v) hE))
    (measure_ne_top_of_subset inter_subset_left hf) (measure_ne_top_of_subset inter_subset_left hf)
  have htr : T v (E ∩ T (u-v) E) = T v E ∩ T u E := by
    ext z
    change (z+v ∈ E ∧ z+v+(u-v) ∈ E) ↔ (z+v ∈ E ∧ z+u ∈ E)
    rw [show z+v+(u-v)=z+u by abel]
  have hsub : X ∩ Y ⊆ T v E ∩ T u E := fun z hz => ⟨hz.2.2,hz.1.2⟩
  have hTf : μ (T v E) ≠ ⊤ := by simpa only [T, measure_preimage_add_right] using hf
  have hb := measureReal_mono (μ := μ) hsub (measure_ne_top_of_subset inter_subset_left hTf)
  rw [← htr,hT] at hb
  change μ.real (X ∩ Y) ≤ ov μ E (u-v) at hb
  change μ.real X + μ.real Y - μ.real E ≤ _
  linarith

private theorem coset_of_bad_pairs {E : Set G} (hE : MeasurableSet E) (hp : 0 < μ E)
    (hf : μ E ≠ ⊤) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/100)
    (hbad : (μ.prod μ).real {z : G × G | z.1 ∈ E ∧ z.2 ∈ E ∧
      ov μ E (z.2-z.1) < (1-a)*μ.real E} < a*(μ.real E)^2) :
    ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
      μ.real (E ∆ {x | x-x₀ ∈ H}) ≤ (8*a)*μ.real E ∧
        |μ.real (H : Set G)-μ.real E| ≤ (8*a)*μ.real E := by
  let m := μ.real E
  have hm : 0 < m := ENNReal.toReal_pos hp.ne' hf
  let L : Set (G × G) := {z | z.1 ∈ E ∧ z.2 ∈ E ∧ ov μ E (z.2-z.1) < (1-a)*m}
  have hL : MeasurableSet L := (measurable_fst hE).inter ((measurable_snd hE).inter
    (measurableSet_lt ((measurable_ov μ hE).comp (measurable_snd.sub measurable_fst)) measurable_const))
  have hfEE : (μ.prod μ) (E ×ˢ E) ≠ ⊤ := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hf hf
  have hLf := measure_ne_top_of_subset (show L ⊆ E ×ˢ E from fun z hz => ⟨hz.1,hz.2.1⟩) hfEE
  obtain ⟨c,hc,hsmall⟩ : ∃ c ∈ E, μ.real (Prod.mk c ⁻¹' L) < a*m := by
    by_contra! hall
    have J := fiber_mass_bound μ L hL hLf E hE (a*m) (by positivity) hall
    change (μ.prod μ).real L < a*m^2 at hbad
    change (a*m)*m ≤ _ at J
    nlinarith
  let S := E \ (Prod.mk c ⁻¹' L)
  have hB : MeasurableSet (Prod.mk c ⁻¹' L) := hL.preimage (measurable_const.prodMk measurable_id)
  have subB : Prod.mk c ⁻¹' L ⊆ E := fun x hx => hx.2.1
  have hSf := measure_ne_top_of_subset (show S ⊆ E from sdiff_subset) hf
  have hSm : (1-a)*m < μ.real S := by
    rw [show μ.real S = m - μ.real (Prod.mk c ⁻¹' L) from measureReal_sdiff subB hB hf]
    linarith
  have hscale : 0 < (1-2*a)*m := mul_pos (by linarith) hm
  have cutoff : ENNReal.ofReal ((1-2*a)*m) < μ S :=
    (ENNReal.ofReal_lt_iff_lt_toReal hscale.le hSf).2 (by
      change _ < μ.real S
      nlinarith [mul_pos ha hm])
  obtain ⟨A,hAS,hAc,hAm⟩ := (hE.diff hB).exists_lt_isCompact_of_ne_top hSf cutoff
  have hAp : 0 < μ A := lt_of_le_of_lt bot_le hAm
  have hAr : (1-2*a)*m < μ.real A :=
    (ENNReal.ofReal_lt_iff_lt_toReal hscale.le hAc.measure_ne_top).mp hAm
  have hAE : A ⊆ E := hAS.trans sdiff_subset
  have good (x : G) (hx : x ∈ A) : (1-a)*m ≤ ov μ E (x-c) :=
    le_of_not_gt fun hh => (hAS hx).2 ⟨hc,hAE hx,hh⟩
  let D := A-A
  have hd : IsCompact D := by
    have eq : (fun z : G × G => z.1-z.2) '' (A ×ˢ A) = D := by
      ext t
      constructor
      · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
        exact ⟨u,hu,v,hv,rfl⟩
      · rintro ⟨u,hu,v,hv,rfl⟩
        exact ⟨(u,v),⟨hu,hv⟩,rfl⟩
    rw [← eq]
    exact (hAc.prod hAc).image continuous_sub
  let P : Set (G × G) := {z | z.2 ∈ E ∧ z.2+z.1 ∈ E}
  have hP : MeasurableSet P := (measurable_snd hE).inter ((measurable_snd.add measurable_fst) hE)
  have pm : (μ.prod μ) P = μ E * μ E :=
    ((measurePreserving_prod_add_swap μ μ).measure_preimage (hE.prod hE).nullMeasurableSet).trans
      (Measure.prod_prod E E)
  have upper := fiber_mass_bound μ P hP (pm ▸ ENNReal.mul_ne_top hf hf) D hd.isClosed.measurableSet
    ((1-2*a)*m) hscale.le (by
      rintro _ ⟨x,hx,y,hy,rfl⟩
      have J := ov_diff μ hE hf (x-c) (y-c)
      rw [show x-c-(y-c)=x-y by abel] at J
      change (1-2*a)*m ≤ ov μ E (x-y)
      change _ - m ≤ _ at J
      linarith [good x hx,good y hy])
  have pmr : (μ.prod μ).real P = m^2 := by
    rw [measureReal_def,pm,ENNReal.toReal_mul,pow_two]; rfl
  rw [pmr] at upper
  have scaled : (1-2*a)*μ.real D ≤ m := by
    apply le_of_mul_le_mul_left (a := m) _ hm
    nlinarith only [upper]
  have hD : μ.real D ≤ (1+3*a)*m := by
    apply le_of_mul_le_mul_left (a := 1-2*a) _ (by linarith)
    have hh : 1 ≤ (1-2*a)*(1+3*a) := by nlinarith [mul_nonneg ha.le (show 0 ≤ 1-6*a by linarith)]
    nlinarith only [scaled,mul_le_mul_of_nonneg_right hh hm.le]
  have hsmallD : μ.real D < (3/2)*μ.real A := by
    nlinarith [mul_lt_mul_of_pos_right (show 1+3*a < 3/2*(1-2*a) by linarith) hm]
  obtain ⟨H,hH,hcomp,hopen⟩ := compact_open_subgroup_of_small_difference μ A hAc hAp hsmallD
  obtain ⟨x₀,hx₀⟩ := nonempty_of_measure_ne_zero hAp.ne'
  let C : Set G := {x | x-x₀ ∈ H}
  have hAC : A ⊆ C := fun x hx => by
    change x-x₀ ∈ (H : Set G); rw [hH]; exact ⟨x,hx,x₀,hx₀,rfl⟩
  have hC : MeasurableSet C := (measurable_id.sub_const x₀) hopen.measurableSet
  have mass : μ C = μ (H : Set G) := by
    change μ ((fun x : G => x-x₀) ⁻¹' (H : Set G)) = _
    simpa only [sub_eq_add_neg] using measure_preimage_add_right μ (-x₀) (H : Set G)
  have cr : μ.real C = μ.real D := by rw [measureReal_def,mass,hH]; rfl
  have cf : μ C ≠ ⊤ := mass ▸ hcomp.measure_ne_top
  have hI := measureReal_mono (μ := μ) (show A ⊆ E ∩ C from subset_inter hAE hAC)
    (measure_ne_top_of_subset inter_subset_left hf)
  have hcA := measureReal_mono (μ := μ) hAC cf
  rw [cr] at hcA
  refine ⟨H,x₀,hcomp,hopen,?_,?_⟩
  · change μ.real (E ∆ C) ≤ 8*a*m
    rw [measureReal_symmDiff_eq hE hC hf cf]
    have J := measureReal_sdiff_add_inter (μ := μ) (s := E) hC hf
    have J' := measureReal_sdiff_add_inter (μ := μ) (s := C) hE cf
    rw [inter_comm C E,cr] at J'
    change _ + _ = m at J
    nlinarith [mul_pos ha hm]
  · rw [hH,abs_le]
    change _ ≤ μ.real D - m ∧ μ.real D - m ≤ _
    constructor <;> nlinarith [mul_pos ha hm]

private def ovE (E : Set G) (t : G) := μ (E ∩ (fun z => z+t) ⁻¹' E)

omit [T2Space G] in
private theorem measurable_ovE {E : Set G} (hE : MeasurableSet E) :
    Measurable (ovE μ E) :=
  measurable_measure_prodMk_left (ν := μ)
    ((measurable_snd hE).inter ((measurable_snd.add measurable_fst) hE))

omit [T2Space G] in
private theorem indicator_moment_pair {E : Set G} (hE : MeasurableSet E) (k : ℕ) :
    (∫⁻ t, (ovE μ E t)^(k+1) ∂μ) =
      ∫⁻ z in E ×ˢ E, (ovE μ E (z.2-z.1))^k ∂μ.prod μ := by
  classical
  let W : G × G → ℝ≥0∞ := (E ×ˢ E).indicator (fun z => ovE μ E (z.2-z.1)^k)
  have hm : Measurable W := (((measurable_ovE μ hE).comp
    (measurable_snd.sub measurable_fst)).pow_const k).indicator (hE.prod hE)
  rw [← lintegral_indicator (hE.prod hE)]
  change _ = ∫⁻ z, W z ∂μ.prod μ
  rw [← (measurePreserving_prod_add_swap μ μ).lintegral_comp hm,
    lintegral_prod (fun z : G × G => W (z.2,z.2+z.1))
      (hm.comp (measurePreserving_prod_add_swap μ μ).measurable).aemeasurable]
  apply lintegral_congr
  intro t
  let S := E ∩ (fun z => z+t) ⁻¹' E
  have hS : MeasurableSet S := hE.inter ((measurable_id.add_const t) hE)
  have point (x : G) : W (x,x+t) = S.indicator (fun _ => ovE μ E t ^ k) x := by
    by_cases h : x ∈ S
    · have h' : (x,x+t) ∈ E ×ˢ E := h
      simp [W,h',h]
    · have h' : (x,x+t) ∉ E ×ˢ E := h
      simp [W,h',h]
  change ovE μ E t ^ (k+1) = ∫⁻ x, W (x,x+t) ∂μ
  simp_rw [point]
  rw [lintegral_indicator_const hS,pow_succ]
  rfl

omit [T2Space G] in
private theorem coset_moment_bound {E : Set G} (hE : MeasurableSet E) (hp : 0<μ E)
    (hf : μ E ≠ ⊤) {a : ℝ} (ha : 0<a) (ha' : a ≤ 1/100) (k : ℕ)
    (hnear : ENNReal.ofReal (1-a^2/2)*(μ E)^(k+3) ≤
      ∫⁻ t, (ovE μ E t)^(k+2) ∂μ) :
    (μ.prod μ).real {z : G × G | z.1 ∈ E ∧ z.2 ∈ E ∧
      ov μ E (z.2-z.1) < (1-a)*μ.real E} < a*(μ.real E)^2 := by
  classical
  let m := μ.real E
  have hm : 0 < m := ENNReal.toReal_pos hp.ne' hf
  let L : Set (G × G) := {z | z.1 ∈ E ∧ z.2 ∈ E ∧ ov μ E (z.2-z.1) < (1-a)*m}
  let Q := E ×ˢ E
  have hQ : MeasurableSet Q := hE.prod hE
  have sub : L ⊆ Q := fun z hz => ⟨hz.1,hz.2.1⟩
  have hL : MeasurableSet L := (measurable_fst hE).inter ((measurable_snd hE).inter
    (measurableSet_lt ((measurable_ov μ hE).comp (measurable_snd.sub measurable_fst)) measurable_const))
  have qmass : (μ.prod μ) Q = μ E * μ E := Measure.prod_prod E E
  have qfin : (μ.prod μ) Q ≠ ⊤ := qmass ▸ ENNReal.mul_ne_top hf hf
  let W := fun z : G × G => ovE μ E (z.2-z.1) ^ (k+1)
  have hW : Measurable W := (((measurable_ovE μ hE).comp
    (measurable_snd.sub measurable_fst)).pow_const (k+1))
  let A := ENNReal.ofReal a * (μ E)^(k+1)
  have wf (t : G) : ovE μ E t ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hf
  have Af : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf)
  have ovle (t : G) : ov μ E t ≤ m := measureReal_mono inter_subset_left hf
  have hpoint (z : G × G) : W z + L.indicator (fun _ => A) z ≤ (μ E)^(k+1) := by
    let r := ov μ E (z.2-z.1)
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hrm : r ≤ m := ovle _
    by_cases hz : z ∈ L
    · rw [indicator_of_mem hz]
      apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top (wf _),Af⟩)
        (ENNReal.pow_ne_top hf)).mp
      rw [ENNReal.toReal_add (ENNReal.pow_ne_top (wf _)) Af]
      simp only [A,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal ha.le]
      change r^(k+1) + a*m^(k+1) ≤ m^(k+1)
      have hb : r < (1-a)*m := hz.2.2
      have J := mul_le_mul (pow_le_pow_left₀ hr hrm k) hb.le hr (pow_nonneg hm.le k)
      rw [pow_succ,pow_succ]
      nlinarith only [J]
    · rw [indicator_of_notMem hz,add_zero]
      exact pow_le_pow_left' (measure_mono inter_subset_left) _
  have J := lintegral_mono (μ := (μ.prod μ).restrict Q) hpoint
  rw [lintegral_add_left hW,setLIntegral_const,lintegral_indicator_const hL,
    Measure.restrict_apply hL,inter_eq_left.mpr sub,qmass] at J
  rw [indicator_moment_pair μ hE (k+1)] at hnear
  have bound := (add_le_add_left hnear (A*(μ.prod μ) L)).trans J
  have tf := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top hf) (ENNReal.mul_ne_top hf hf)) bound
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf))
    (ENNReal.mul_ne_top Af (measure_ne_top_of_subset sub qfin))] at tf
  have hab : 0 ≤ 1-a^2/2 := by nlinarith [mul_nonneg ha.le (show 0≤1-a by linarith)]
  simp only [A,ENNReal.toReal_mul,ENNReal.toReal_ofReal hab,ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_pow] at tf
  let ℓ := (μ.prod μ).real L
  change (1-a^2/2)*m^(k+3) + (a*m^(k+1))*ℓ ≤ m^(k+1)*(m*m) at tf
  rw [show k+3=(k+1)+2 by omega,pow_add] at tf
  have tj : (m^(k+1))*((1-a^2/2)*m^2 + a*ℓ) ≤ (m^(k+1))*m^2 := by nlinarith only [tf]
  have h := le_of_mul_le_mul_left tj (pow_pos hm _)
  change ℓ < a*m^2
  apply lt_of_mul_lt_mul_left (a := a) _ ha.le
  nlinarith [mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hm)]

/-- The indicator case of inverse Young, uniform over groups and Haar
normalizations. The output controls both symmetric difference and subgroup
mass relative to the original set. -/
theorem indicator_inverse_young (d : ℕ) (hd : 2 ≤ d) (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧
      ∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
      (E : Set G), MeasurableSet E → 0 < μ E → μ E ≠ ⊤ →
      ENNReal.ofReal (1-δ)*(μ E)^(d+1) ≤
        (∫⁻ t, (∫⁻ x, E.indicator (1 : G → ℝ≥0∞) x * E.indicator 1 (x+t) ∂μ)^d ∂μ) →
      ∃ (H : AddSubgroup G) (x₀ : G), IsCompact (H : Set G) ∧ IsOpen (H : Set G) ∧
        μ.real (E ∆ {x | x-x₀ ∈ H}) ≤ η*μ.real E ∧
          |μ.real (H : Set G)-μ.real E| ≤ η*μ.real E := by
  classical
  let a := min (1/100) (η/8)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hsm : a ≤ 1/100 := min_le_left ..
  have hη' : 8*a ≤ η := by linarith only [show a ≤ η/8 from min_le_right ..]
  refine ⟨a^2/2,by positivity,by nlinarith [mul_nonneg ha.le (show 0≤1-a by linarith)],?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ E hE hp hf hnear
  have point (t : G) : (∫⁻ x, E.indicator (1 : G → ℝ≥0∞) x * E.indicator 1 (x+t) ∂μ) =
      ovE μ E t := by
    let S := E ∩ (fun x => x+t) ⁻¹' E
    have hS : MeasurableSet S := hE.inter ((measurable_id.add_const t) hE)
    trans ∫⁻ x, S.indicator (1 : G → ℝ≥0∞) x ∂μ
    · apply lintegral_congr
      intro x
      by_cases hx : x∈E <;> by_cases ht : x+t ∈ E <;> simp [S,hx,ht]
    · exact lintegral_indicator_one hS
  simp_rw [point] at hnear
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [Nat.add_comm 2 k] at hnear
  obtain ⟨H,x₀,hc,ho,hD,hM⟩ := coset_of_bad_pairs μ hE hp hf ha hsm
    (coset_moment_bound μ hE hp hf ha hsm k hnear)
  have h := mul_le_mul_of_nonneg_right hη' (measureReal_nonneg (μ := μ) (s := E))
  exact ⟨H,x₀,hc,ho,hD.trans h,hM.trans h⟩

end LpGowers
