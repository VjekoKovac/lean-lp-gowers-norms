module

public import LpGowers.ClosureLeakage
public import LpGowers.SmallLeakage
public import LpGowers.SquareThreshold
import LpGowers.TensorTransfer
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The two-dimensional rectangle in the proof of Theorem 1.1

The second autocorrelation is invariant under exchanging its two increments.
Intersecting the two sides of a near-extremising rectangle therefore gives
a square approximant. The marginal identity controls its first correlation,
and the diagonal estimate detects a compact open subgroup.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]

private def rect (A B : Set G) : G × G → ℝ≥0∞ := (A ×ˢ B).indicator 1

omit [AddCommGroup G] [MeasurableAdd₂ G] in
private theorem rect_meas {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (rect A B) := measurable_const.indicator (hA.prod hB)

private def R (f : G → ℝ≥0) (z : G×G) : ℝ≥0∞ :=
  autocorrelation μ 2 f ((MeasurableEquiv.finTwoArrow (α:=G)).symm z)

private theorem R_meas {f : G → ℝ≥0} (hf : AEMeasurable f μ) : Measurable (R μ f) :=
  (measurable_autocorrelation_of_aemeasurable μ 2 hf).comp MeasurableEquiv.finTwoArrow.symm.measurable

omit [MeasurableAdd₂ G] [μ.IsAddLeftInvariant] [SigmaFinite μ] in
private theorem R_swap (f : G → ℝ≥0) (z : G × G) : R μ f z.swap = R μ f z := by
  apply lintegral_congr; intro x
  change ((f x : ℝ≥0∞) * (f (x+z.1)) * ((f (x+z.2))*(f (x+z.2+z.1)))) =
    ((f x : ℝ≥0∞) * (f (x+z.2)) * ((f (x+z.1))*(f (x+z.1+z.2))))
  rw [add_right_comm x z.2 z.1]
  ac_rfl

private theorem rect_dist_eq {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
      (fun h => (A ×ˢ B).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1)) =
    l1DensityError (μ.prod μ) (R μ f) (rect A B) := by
  let e : (Fin 2 → G) ≃ᵐ G × G := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (cubeMeasure μ 2) (μ.prod μ) := measurePreserving_finTwoArrow μ
  let D := fun z => (R μ f z - rect A B z) + (rect A B z - R μ f z)
  have hu := R_meas μ hf
  have hw := rect_meas hA hB
  have hD : Measurable D := (hu.sub hw).add (hw.sub hu)
  change _ = ∫⁻ z, D z ∂μ.prod μ
  rw [← he.lintegral_comp hD]
  apply lintegral_congr; intro h
  simp only [D,R,show (MeasurableEquiv.finTwoArrow : (Fin 2 → G) ≃ᵐ G×G) = e from rfl,
    MeasurableEquiv.symm_apply_apply]
  rfl

omit [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] in
private theorem rect_swap (A B : Set G) (z : G × G) : rect B A z = rect A B z.swap := by
  classical
  by_cases h₁ : z.1∈B <;> by_cases h₂ : z.2∈A <;> simp [rect, Set.mem_prod, h₁, h₂]

/-- At any point the square indicator equals either the rectangle indicator
or its transpose. By symmetry of the autocorrelation the two errors have the
same integral. -/
theorem rectangle_to_square {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let E (S T : Set G) := l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
       (fun h => (S ×ˢ T).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1))
    E (A ∩ B) (A ∩ B) ≤ 2 * E A B := by
  classical
  dsimp only
  let K := A ∩ B
  let u := R μ f
  let D (S T : Set G) (z : G × G) := (u z - rect S T z) + (rect S T z - u z)
  rw [rect_dist_eq μ hf (hA.inter hB) (hA.inter hB), rect_dist_eq μ hf hA hB]
  have hu := R_meas μ hf
  have hW := rect_meas hA hB
  have hD : Measurable (D A B) := (hu.sub hW).add (hW.sub hu)
  change (∫⁻ z, D K K z ∂μ.prod μ) ≤ 2*(∫⁻ z, D A B z ∂μ.prod μ)
  have hswap (z : G × G) : D B A z = D A B z.swap := by
    dsimp only [D,u]; rw [rect_swap, R_swap]
  calc
    _ ≤ ∫⁻ z, D A B z + D B A z ∂μ.prod μ := by
      apply lintegral_mono; intro z
      have he : rect K K z = rect A B z ∨ rect K K z = rect B A z := by
        by_cases h₁ : z.1∈A <;> by_cases h₂ : z.2∈B <;> by_cases h₃ : z.2∈A <;>
          by_cases h₄ : z.1∈B <;> simp [K,rect,Set.mem_prod,h₁,h₂,h₃,h₄]
      rcases he with h | h
      · dsimp only [D]; rw [h]; exact le_self_add
      · dsimp only [D]; rw [h]; exact le_add_self
    _ = _ := by
      rw [lintegral_add_left hD]
      simp_rw [hswap]
      rw [lintegral_prod_swap, two_mul]

private theorem mass_le_error {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {u v : X → ℝ≥0∞} (hv : Measurable v) :
    (∫⁻ x, u x ∂ν) ≤ (∫⁻ x, v x ∂ν) + l1DensityError ν u v := by
  rw [l1DensityError, ← lintegral_add_left hv]
  apply lintegral_mono; intro x
  exact (le_add_tsub (a:=u x) (b:=v x)).trans (add_le_add_right le_self_add _)

omit [AddCommGroup G] [MeasurableAdd₂ G] [μ.IsAddLeftInvariant] in
private theorem rect_mass {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ z, rect A B z ∂μ.prod μ) = μ A * μ B := by
  change (∫⁻ z, (A ×ˢ B).indicator (fun _ => (1:ℝ≥0∞)) z ∂μ.prod μ) = _
  rw [lintegral_indicator_const (hA.prod hB), one_mul, Measure.prod_prod]

/-- The area lost when the rectangle is intersected with its transpose is at
most three times the original approximation error. -/
theorem rectangle_mass_le_square {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ A * μ B ≤ μ (A∩B) * μ (A∩B) + 3*l1DensityError (cubeMeasure μ 2)
      (autocorrelation μ 2 f) (fun h => (A×ˢB).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1)) := by
  let K := A ∩ B
  have hK := hA.inter hB
  have H := rectangle_to_square μ hf hA hB
  dsimp only at H
  rw [rect_dist_eq μ hf hK hK, rect_dist_eq μ hf hA hB] at H
  rw [rect_dist_eq μ hf hA hB, ← rect_mass μ hA hB, ← rect_mass μ hK hK]
  let ν := μ.prod μ
  have hswap : l1DensityError ν (rect A B) (R μ f) = l1DensityError ν (R μ f) (rect A B) := by
    unfold l1DensityError; simp only [add_comm]
  have he := l1DensityError_triangle ν (rect_meas hA hB) (R_meas μ hf) (rect_meas hK hK)
  rw [hswap] at he
  apply (mass_le_error ν (rect_meas hK hK)).trans
  apply add_le_add_right
  apply he.trans
  calc
    _ ≤ _ := add_le_add_right H _
    _ = _ := by ring

private theorem square_deficit {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {K : Set G} (hK : MeasurableSet K) :
    (∫⁻ x in K, μ K - (pairCorrelation μ (liftNN f) (liftNN f) x)^2 ∂μ) ≤
      l1DensityError (μ.prod μ) (R μ f) (rect K K) := by
  classical
  let u := R μ f
  let w := rect K K
  let v := pairCorrelation μ (liftNN f) (liftNN f)
  let D := fun z => (u z - w z) + (w z-u z)
  have hu := R_meas μ hf
  have hw := rect_meas hK hK
  have hD : Measurable D := (hu.sub hw).add (hw.sub hu)
  change _ ≤ ∫⁻ z, D z ∂μ.prod μ
  rw [lintegral_prod_symm' D hD]
  apply le_trans _ (lintegral_mono_set (s:=K) (t:=Set.univ) (Set.subset_univ _) |>.trans_eq (by rw [Measure.restrict_univ]))
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hK] with x hx
  have h₁ : (∫⁻ y, u (y,x) ∂μ) = (v x)^2 := by
    convert! autocorrelation_marginal μ hf 1 0 (fun _ => x) using 1
  have h₂ : (∫⁻ y, w (y,x) ∂μ) = μ K := by
    have hp (y : G) : w (y,x) = K.indicator (fun _ => (1:ℝ≥0∞)) y := by
      by_cases hy : y∈K <;> simp [w,rect,hx,hy,Set.mem_prod]
    simp_rw [hp]
    simp [lintegral_indicator_const hK]
  change μ K - (v x)^2 ≤ _
  rw [← h₁, ← h₂]
  exact (lintegral_sub_le _ _ (hu.comp (measurable_id.prodMk measurable_const))).trans
    (lintegral_mono (fun _ => le_add_self))

/-- The mass of the first autocorrelation off the square's generating set.
On the set the shortfall of its square controls its shortfall below one. -/
theorem tail_of_square {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    {K : Set G} (hK : MeasurableSet K) (hfin : μ K ≠ ⊤) :
    let v := pairCorrelation μ (liftNN f) (liftNN f)
    (∫⁻ x in Kᶜ, v x ∂μ) ≤ (∫⁻ x, liftNN f x ∂μ)^2 +
       (μ K * (1 - μ K) + l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
          (fun h => (K×ˢK).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1))) - μ K := by
  let m := μ K
  let v := pairCorrelation μ (liftNN f) (liftNN f)
  have hv : Measurable v := (measurable_autocorrelation_of_aemeasurable μ 1 hf).comp
    (show Measurable (fun t : G => fun _ : Fin 1 => t) from measurable_pi_iff.mpr fun _ => measurable_id)
  have hmass : m ≤ (∫⁻ x in K, v x ∂μ) + (m*(1-m) + ∫⁻ x in K, m-(v x)^2 ∂μ) := by
    have point (x : G) : 1 ≤ v x + ((1-m) + (m-(v x)^2)) := by
      by_cases hx : v x ≤ 1
      · have hsq : (v x)^2 ≤ v x := by simpa only [sq, one_mul] using mul_le_mul_left hx (v x)
        calc
          1 ≤ (1-m)+m := le_tsub_add
          _ ≤ (1-m)+((v x)^2+(m-(v x)^2)) := add_le_add_right le_add_tsub _
          _ ≤ (1-m)+(v x+(m-(v x)^2)) := by gcongr
          _ = _ := by ac_rfl
      · exact (le_of_not_ge hx).trans le_self_add
    have h := lintegral_mono (μ:=μ.restrict K) point
    simpa only [lintegral_add_left hv, lintegral_add_left measurable_const,
      lintegral_const, Measure.restrict_apply_univ, one_mul, mul_comm (1-m) (μ K)] using h
  rw [rect_dist_eq μ hf hK hK]
  apply ENNReal.le_sub_of_add_le_left hfin
  calc
    _ ≤ ((∫⁻ x in K, v x ∂μ) + (m*(1-m) + ∫⁻ x in K, m-(v x)^2 ∂μ)) + ∫⁻ x in Kᶜ, v x ∂μ :=
      add_le_add_left hmass _
    _ = (∫⁻ x, v x ∂μ) + (m*(1-m) + ∫⁻ x in K, m-(v x)^2 ∂μ) := by
      rw [add_right_comm, lintegral_add_compl _ hK]
    _ ≤ _ := by rw [pairCorrelation_self_mass μ hf]; gcongr; exact square_deficit μ hf hK

/-- The two-dimensional closure defect is bounded using only the approximating
rectangle, the mass of the sliced input, and its third Gowers norm. -/
theorem leakage_from_rectangle [MeasurableNeg G] [μ.IsNegInvariant]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A B : Set G} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : μ (A∩B) ≠ ⊤) {e : ℝ≥0∞}
    (hE : l1DensityError (cubeMeasure μ 2) (autocorrelation μ 2 f)
      (fun h => (A×ˢB).indicator (1 : G×G → ℝ≥0∞) (h 0,h 1)) ≤ e)
    (hU : (ordinaryGowers μ 3 f)^2 ≤ 2) :
    let K := A∩B
    let F := ∫⁻ x, liftNN f x ∂μ
    let m := μ K
    μ.prod μ {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K} ≤
      2*e + (F^2 + (m*(1-m)+2*e) - m)^(1/2:ℝ)*F*2 := by
  let K := A∩B
  have hK := hA.inter hB
  have hh := rectangle_to_square μ hf hA hB
  dsimp only at hh
  have H := hh.trans (mul_le_mul_right hE 2)
  have ht := tail_of_square μ hf hK hfin
  apply (measure_bad_pairs_le μ hf hK).trans
  apply add_le_add H
  rw [lp]
  simp only [div_one, ENNReal.rpow_one]
  apply mul_le_mul' _ hU
  apply mul_le_mul_left
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply ht.trans
  gcongr

private theorem compact_open_of_leakage_ennreal {X : Type*}
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.IsAddHaarMeasure]
    {K : Set X} (hK : MeasurableSet K) (hpos : 0 < ν K) (hfin : ν K ≠ ⊤)
    (h : ν.prod ν {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.1+z.2 ∉ K} < (ν K)^2 / 100) :
    ∃ H : AddSubgroup X, IsCompact (H : Set X) ∧ IsOpen (H : Set X) := by
  apply compact_open_subgroup_of_small_additive_leakage ν K hK hpos hfin
  have hr := (ENNReal.toReal_lt_toReal (ne_top_of_lt h) (by finiteness)).mpr h
  simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using hr

section CompactOpen

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [ν.IsAddHaarMeasure]

/-- Absolute two-dimensional threshold in §6. A rectangle with sides close
to unit measure and small error for the second autocorrelation forces a
compact open subgroup. -/
theorem compact_open_of_rectangle {f : X → ℝ≥0} (hf : AEMeasurable f ν)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha₀ : 1-(1/10^12:ℝ≥0∞) ≤ ν A) (ha₁ : ν A ≤ 1+(1/10^12:ℝ≥0∞))
    (hb₀ : 1-(1/10^12:ℝ≥0∞) ≤ ν B) (hb₁ : ν B ≤ 1+(1/10^12:ℝ≥0∞))
    (hmass : (∫⁻ x, liftNN f x ∂ν) ≤ 1+(1/10^12:ℝ≥0∞))
    (hError : l1DensityError (cubeMeasure ν 2) (autocorrelation ν 2 f)
      (fun h => (A×ˢB).indicator (1 : X×X → ℝ≥0∞) (h 0,h 1)) ≤ 1/10^12)
    (hU : (ordinaryGowers ν 3 f)^2 ≤ 2) :
    ∃ H : AddSubgroup X, IsCompact (H : Set X) ∧ IsOpen (H : Set X) := by
  let K := A ∩ B
  let t : ℝ≥0∞ := 1 / 10^12
  have hKA : ν K ≤ ν A := measure_mono Set.inter_subset_left
  have hfin : ν K ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (1+(1/10^12:ℝ≥0∞)) ≠ ⊤) (hKA.trans ha₁)
  have harea : ν A * ν B ≤ ν K * ν K + 3*t :=
    (rectangle_mass_le_square ν hf hA hB).trans (add_le_add_right (mul_le_mul_right hError 3) _)
  have hleak := leakage_from_rectangle ν hf hA hB hfin hError hU
  obtain ⟨hpos,_,hlt⟩ := square_leakage_threshold ha₀ hb₀ ha₁ hb₁ harea hKA hmass hleak
  exact compact_open_of_leakage_ennreal ν (hA.inter hB) hpos hfin hlt

end CompactOpen

end LpGowers
