module

public import LpGowers.YoungPlateau

/-! # Normalizing the plateau in inverse Young

The integral of an approximate plateau differs from one by at most its
L¹ error. Correcting its height therefore costs at most the same error.
Taking an appropriate nonnegative power gives the unit Lˢ indicator. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The unit Lˢ indicator, with its amplitude determined by the set's mass. -/
def unitIndicator (s : ℝ) (E : Set X) : X → ℝ≥0 :=
  E.indicator (fun _ => (μ E).toNNReal ^ (-(1/s)))

theorem measurable_unitIndicator {E : Set X} (hE : MeasurableSet E) (s : ℝ) :
    Measurable (unitIndicator μ s E) := measurable_const.indicator hE

private theorem lpDist_one_triangle (f g h : X → ℝ≥0) (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : lpDist μ 1 f h ≤ lpDist μ 1 f g + lpDist μ 1 g h := by
  simp only [lpDist,lp,div_one,ENNReal.rpow_one]
  rw [← lintegral_add_left' (hf.edist hg)]
  exact lintegral_mono fun x => edist_triangle (f x) (g x) (h x)

private theorem lpDist_one_comm (f g : X → ℝ≥0) : lpDist μ 1 f g = lpDist μ 1 g f := by
  simp only [lpDist]
  congr 1
  funext x
  exact edist_comm ..

private theorem lpDist_one_zero (f : X → ℝ≥0) :
    lpDist μ 1 f (fun _ => 0) = ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
  simp only [lpDist,lp,div_one,ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [edist_dist,NNReal.dist_eq,NNReal.coe_zero,sub_zero,abs_of_nonneg (f x).coe_nonneg]
  exact ENNReal.ofReal_coe_nnreal

private theorem indicator_mass {E : Set X} (hE : MeasurableSet E) (c : ℝ≥0) :
    (∫⁻ x, (↑(E.indicator (fun _ => c) x):ℝ≥0∞) ∂μ) = c * μ E := by
  have he (x) : (↑(E.indicator (fun _ => c) x):ℝ≥0∞) =
      E.indicator (fun _ => (c:ℝ≥0∞)) x := by by_cases h : x∈E <;> simp [h]
  simp_rw [he]
  rw [lintegral_indicator hE,setLIntegral_const]

private theorem indicator_l1_distance {E : Set X} (hE : MeasurableSet E) (c b : ℝ≥0) :
    lpDist μ 1 (E.indicator fun _ => c) (E.indicator fun _ => b) = edist c b * μ E := by
  have he (x) : edist (E.indicator (fun _ => c) x) (E.indicator (fun _ => b) x) =
      E.indicator (fun _ => edist c b) x := by by_cases h : x∈E <;> simp [h]
  simp only [lpDist,lp,div_one,ENNReal.rpow_one]
  simp_rw [he]
  rw [lintegral_indicator hE,setLIntegral_const]

/-- Normalizing a plateau of a unit density multiplies its error by at most
two. Finiteness and positivity of the set's measure both follow from the
strictly subunit error. -/
theorem normalize_young_plateau {u : X → ℝ≥0} (hu : AEMeasurable u μ)
    (hI : (∫⁻ x, (u x:ℝ≥0∞) ∂μ)=1) {E : Set X} (hE : MeasurableSet E)
    {c : ℝ≥0} (hc : 0<c) {η : ℝ} (hη : 0≤η) (hη1 : η<1)
    (hnear : lpDist μ 1 u (E.indicator (fun _ => c)) ≤ ENNReal.ofReal η) :
    0 < μ E ∧ μ E ≠ ⊤ ∧ lpDist μ 1 u (unitIndicator μ 1 E) ≤ ENNReal.ofReal (2*η) := by
  let P := E.indicator (fun _ => c)
  have hP : Measurable P := measurable_const.indicator hE
  let A := (c:ℝ≥0∞)*μ E
  have hPm : lpDist μ 1 P (fun _ => 0) = A :=
    (lpDist_one_zero μ P).trans (indicator_mass μ hE c)
  have hu0 : lpDist μ 1 u (fun _ => 0) = 1 := (lpDist_one_zero μ u).trans hI
  have hA : A ≤ ENNReal.ofReal η + 1 := by
    have h := lpDist_one_triangle μ P u (fun _ => 0) hP.aemeasurable hu
    rw [hPm,hu0,lpDist_one_comm μ P u] at h
    exact h.trans (add_le_add_left hnear _)
  have h1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal η + A := by
    have h := lpDist_one_triangle μ u P (fun _ => 0) hu hP.aemeasurable
    rw [hPm,hu0] at h
    exact h.trans (add_le_add_left hnear _)
  have hAfin : A ≠ ⊤ := (hA.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,ENNReal.one_lt_top⟩)).ne
  have hfin : μ E ≠ ⊤ := by
    intro ht
    apply hAfin
    simp [A,ht,show (c:ℝ≥0∞) ≠ 0 by exact_mod_cast hc.ne']
  have hpos : 0< μ E := by
    by_contra! hz
    have hAz : A = 0 := by simp [A,le_antisymm hz zero_le]
    rw [hAz,add_zero] at h1
    exact (ENNReal.ofReal_lt_one.mpr hη1).not_ge h1
  let b := (μ E).toNNReal
  have hb : 0<b := ENNReal.toNNReal_pos hpos.ne' hfin
  have hb' : 0<(b:ℝ) := hb
  have hEb : (b:ℝ≥0∞) = μ E := ENNReal.coe_toNNReal hfin
  have hAb : A.toReal = (c:ℝ)*(b:ℝ) := by rw [show A = (c:ℝ≥0∞)*(b:ℝ≥0∞) by rw [hEb],ENNReal.toReal_mul]; rfl
  have hmass : |(c:ℝ)*(b:ℝ)-1| ≤ η := by
    rw [← hAb,abs_le]
    have hi := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hAfin⟩) h1
    have hj := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.one_ne_top⟩) hA
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hAfin, ENNReal.toReal_one, ENNReal.toReal_ofReal hη] at hi
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal hη] at hj
    constructor <;> linarith
  have hN : unitIndicator μ 1 E = E.indicator (fun _ => b⁻¹) := by simp [unitIndicator,b, NNReal.rpow_neg]
  have hd : lpDist μ 1 P (unitIndicator μ 1 E) ≤ ENNReal.ofReal η := by
    rw [hN,indicator_l1_distance μ hE,← hEb,edist_dist,NNReal.dist_eq,NNReal.coe_inv,
      ← ENNReal.ofReal_coe_nnreal (p:=b),← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have he : |(c:ℝ)-(b:ℝ)⁻¹| *(b:ℝ) = |(c:ℝ)*(b:ℝ)-1| := by
      calc
        _ = |((c:ℝ)-(b:ℝ)⁻¹)*(b:ℝ)| := by rw [abs_mul,abs_of_pos hb']
        _ = _ := by rw [sub_mul,inv_mul_cancel₀ hb'.ne']
    exact he.le.trans hmass
  refine ⟨hpos,hfin,(lpDist_one_triangle μ u P _ hu hP.aemeasurable).trans ?_⟩
  refine (add_le_add hnear hd).trans_eq ?_
  rw [← ENNReal.ofReal_add hη hη]
  congr 1
  ring


/-- The power changing L¹ to Lˢ takes normalized indicators to normalized
indicators of the same set. -/
theorem unitIndicator_root (s : ℝ) (hs : 0<s) (E : Set X) :
    (fun x => unitIndicator μ 1 E x ^ (1/s)) = unitIndicator μ s E := by
  funext x
  by_cases hx : x∈E
  · simp only [unitIndicator,Set.indicator_of_mem hx,div_one,← NNReal.rpow_mul]
    congr 1
    ring
  · simp only [unitIndicator,Set.indicator_of_notMem hx,NNReal.zero_rpow (one_div_pos.mpr hs).ne']

theorem unitIndicator_unit_moment {s : ℝ} (hs : 0<s) {E : Set X} (hE : MeasurableSet E)
    (hpos : 0<μ E) (hfin : μ E ≠ ⊤) :
    (∫⁻ x, (unitIndicator μ s E x : ℝ≥0∞)^s ∂μ) = 1 := by
  have hpoint (x) : (unitIndicator μ s E x : ℝ≥0∞)^s =
      E.indicator (fun _ => (μ E)⁻¹) x := by
    by_cases hx : x∈E
    · simp only [unitIndicator,Set.indicator_of_mem hx]
      rw [ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_pos hpos.ne' hfin).ne',
        ENNReal.coe_toNNReal hfin, ← ENNReal.rpow_mul,neg_mul,one_div_mul_cancel hs.ne',
        ENNReal.rpow_neg_one]
    · simp [unitIndicator,hx,ENNReal.zero_rpow_of_pos hs]
  simp_rw [hpoint]
  rw [lintegral_indicator hE,setLIntegral_const,ENNReal.inv_mul_cancel hpos.ne' hfin]

/-- Near maximizers of the integer-output Young autocorrelation are close
to a unit indicator in their original Lˢ norm. This statement includes all
functions measurable for the completion of the given measure. -/
theorem exists_unit_young_indicator.{u} (d : ℕ) (hd : 2≤d) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (G : Type u) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
        (μ : Measure G) [SigmaFinite μ] [μ.IsAddLeftInvariant] (f : G → ℝ≥0), AEMeasurable f μ →
      let s := 2*(d:ℝ)/(d+1)
      (∫⁻ x, (f x : ℝ≥0∞)^s ∂μ) = 1 →
      ENNReal.ofReal (1-δ) ≤ ∫⁻ a, (∫⁻ x, (f x : ℝ≥0∞)*f (x+a) ∂μ)^(d:ℝ) ∂μ →
      ∃ E : Set G, MeasurableSet E ∧ 0<μ E ∧ μ E ≠ ⊤ ∧
        (∫⁻ x, (unitIndicator μ s E x : ℝ≥0∞)^s ∂μ) = 1 ∧
        lpDist μ s f (unitIndicator μ s E) ≤ ENNReal.ofReal ε := by
  have hD : (0:ℝ) < d := by exact_mod_cast (by omega : 0<d)
  let s := 2*(d:ℝ)/(d+1)
  have hs : 0<s := by dsimp [s]; positivity
  obtain ⟨τ,hτ,hpow⟩ := power_transfer_tolerance.{u} (r:=1) (by norm_num)
    (one_div_pos.mpr hs) hε
  let η := min (τ/2) (1/2)
  have hη : 0<η := lt_min (half_pos hτ) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hητ : 2*η ≤ τ := by linarith only [min_le_left (τ/2) (1/2)]
  obtain ⟨δ,hδ,hδ1,hflat⟩ := exists_young_plateau.{u} d hd η hη
  refine ⟨δ,hδ,hδ1,?_⟩
  intro G _ _ _ ν _ _ f hf _ hmass hnear
  let F := hf.mk f
  have hF : Measurable F := hf.measurable_mk
  have he : f =ᵐ[ν] F := hf.ae_eq_mk
  have hmassF : (∫⁻ x, (F x : ℝ≥0∞)^s ∂ν) = 1 := by
    rw [← hmass]; apply lintegral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have hcor (a : G) : (∫⁻ x, (f x:ℝ≥0∞)*f (x+a) ∂ν) = ∫⁻ x, (F x:ℝ≥0∞)*F (x+a) ∂ν := by
    apply lintegral_congr_ae
    have ha := (measurePreserving_add_right ν a).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [he,ha] with x hx hy
    change f (x+a) = F (x+a) at hy
    rw [hx,hy]
  simp_rw [hcor] at hnear
  obtain ⟨E,c,hE,hc,herr⟩ := hflat G ν F hF hmassF hnear
  let U := fun x => F x ^ s
  have hUI : (∫⁻ x, (U x : ℝ≥0∞) ∂ν) = 1 := by
    simpa only [U,ENNReal.coe_rpow_of_nonneg _ hs.le] using hmassF
  obtain ⟨hpos,hfin,hclose⟩ := normalize_young_plateau ν (hF.pow_const s).aemeasurable hUI hE
    hc hη.le hη1 herr
  have hpow' := hpow G ν U (unitIndicator ν 1 E) (hF.pow_const s).aemeasurable
    (measurable_unitIndicator ν hE 1).aemeasurable (by simpa only [ENNReal.rpow_one] using hUI)
    (unitIndicator_unit_moment ν (by norm_num) hE hpos hfin)
    (hclose.trans (ENNReal.ofReal_le_ofReal hητ))
  have hr : (fun x => U x ^ (1/s))=F := by
    funext x
    simp [U, ← NNReal.rpow_mul,hs.ne']
  rw [one_div_one_div,hr,unitIndicator_root ν s hs E] at hpow'
  have hdEq : lpDist ν s f (unitIndicator ν s E) = lpDist ν s F (unitIndicator ν s E) := by
    unfold lpDist lp
    congr 1
    apply lintegral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  exact ⟨E,hE,hpos,hfin,unitIndicator_unit_moment ν hs hE hpos hfin,hdEq.le.trans hpow'⟩

end LpGowers
