module

public import LpGowers.MomentControl
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Near rigidity for three moments

Lemma 6.2 of Kovač–Rogers. The proof uses the same threshold set as the paper,
`{x | 1/2 < F x}`. Bounding the errors at both endpoint powers makes one
tolerance work for every intermediate exponent. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LpGowers

private theorem moment_error_uniform {a c η : ℝ} (ha : 0 < a) (hac : a < c)
    (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ∀ t : ℝ, a ≤ t → t ≤ c →
      |x - (if 1/2 < x then 1 else 0)| ^ t + |x^c - (if 1/2 < x then 1 else 0)| ≤
        η * (x^a+x^c) + C * (Real.sqrt (x^a) - Real.sqrt (x^c))^2 := by
  obtain ⟨A,hA,h⟩ := moment_error_domination ha hac le_rfl hac.le hη
  obtain ⟨B,hB,g⟩ := moment_error_domination ha hac hac.le le_rfl hη
  refine ⟨max A B,hA.trans (le_max_left ..),?_⟩
  intro x hx t hat htc
  let z := |x - (if 1/2 < x then 1 else 0)|
  by_cases hz : z ≤ 1
  · have he := add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left A B)
        (sq_nonneg (Real.sqrt (x^a) - Real.sqrt (x^c)))) (η*(x^a+x^c))
    apply (le_trans _ ((h x hx).trans he))
    exact add_le_add_left (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hz ha.le hat) _
  · have he := add_le_add_right (mul_le_mul_of_nonneg_right (le_max_right A B)
        (sq_nonneg (Real.sqrt (x^a) - Real.sqrt (x^c)))) (η*(x^a+x^c))
    apply (le_trans _ ((g x hx).trans he))
    exact add_le_add_left (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hz) htc) _

/-- Three moments near one force proximity to an indicator in every intermediate
power, and the measure of the same set is near one. The threshold depends only
on `a,b,c,η`, uniformly over all measures, functions and `t ∈ [a,c]`. -/
theorem three_moments_near {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ), 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ),
    Measurable F → (∀ x, 0 ≤ F x) →
    (∀ s ∈ ({a,b,c} : Set ℝ), Integrable (fun x => F x ^ s) μ ∧
      |(∫ x, F x ^ s ∂μ) - 1| ≤ ε) →
    let E := {x | 1/2 < F x}
    MeasurableSet E ∧ μ E < ⊤ ∧ |μ.real E - 1| ≤ η ∧
      ∀ t ∈ Set.Icc a c, Integrable (fun x => |F x - E.indicator 1 x| ^ t) μ ∧
        (∫ x, |F x - E.indicator 1 x| ^ t ∂μ) ≤ η := by
  have hac := hab.trans hbc
  have hc := ha.trans hac
  let θ := (c-b)/(c-a)
  have hθ : 0 < θ := div_pos (sub_pos.mpr hbc) (sub_pos.mpr hac)
  have hθ' : θ < 1 := (div_lt_one (sub_pos.mpr hac)).mpr (by linarith)
  have hmix : a*θ + c*(1-θ) = b := by
    dsimp [θ]
    field_simp [ne_of_gt (sub_pos.mpr hac)]
    ring
  let w := min θ (1-θ)
  have hw : 0 < w := lt_min hθ (sub_pos.mpr hθ')
  let τ := η/16
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨C,hC,control⟩ := moment_error_uniform ha hac hτ
  let L := C*2/w+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨min 1 (η/(2*L)),lt_min (by norm_num) (div_pos hη (by positivity)),?_⟩
  intro ε hε hεδ X _ μ F hF hn hm
  have hε1 := (lt_min_iff.mp hεδ).1
  have hεL := (lt_div_iff₀ (show 0 < 2*L by positivity)).mp ((lt_min_iff.mp hεδ).2)
  let E := {x | 1/2 < F x}
  let I : X → ℝ := E.indicator 1
  have hE : MeasurableSet E := measurableSet_lt measurable_const hF
  have mI : Measurable I := measurable_const.indicator hE
  have iEq (x : X) : I x = (if 1/2 < F x then 1 else 0) := by
    classical
    simp only [I,E,Set.indicator_apply,Set.mem_ofPred_eq,Pi.one_apply]
  let A (x : X) := F x ^ a
  let B (x : X) := F x ^ b
  let Z (x : X) := F x ^ c
  have ⟨hA,hMa⟩ := hm a (by simp)
  have ⟨hB,hMb⟩ := hm b (by simp)
  have ⟨hZ,hMz⟩ := hm c (by simp)
  have hMa' := (abs_le.mp hMa).2
  have hMz' := (abs_le.mp hMz).2
  have hMb' := (abs_le.mp hMb).1
  let D (x : X) := (Real.sqrt (A x) - Real.sqrt (Z x))^2
  have hiD : Integrable D μ := by
    apply (hA.add hZ).mono' ((hA.aemeasurable.sqrt.sub hZ.aemeasurable.sqrt).pow_const 2).aestronglyMeasurable
    filter_upwards with x
    change ‖(Real.sqrt (A x) - Real.sqrt (Z x))^2‖ ≤ A x + Z x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sq_sqrt (Real.rpow_nonneg (hn x) a),Real.sq_sqrt (Real.rpow_nonneg (hn x) c),
      mul_nonneg (Real.sqrt_nonneg (A x)) (Real.sqrt_nonneg (Z x))]
  have hdB : w * (∫ x, D x ∂μ) ≤ 2*ε := three_moment_sqrt_deficit μ
    (Filter.Eventually.of_forall hn) ha.le hc.le hθ.le hθ'.le hmix hA hZ (by linarith) (by linarith) (by linarith)
  have hd := (le_div_iff₀ hw).mpr (by linarith : (∫ x,D x ∂μ)*w ≤ 2*ε)
  let S (x : X) := τ*(A x+Z x)+C*D x
  have hiS : Integrable S μ := ((hA.add hZ).const_mul τ).add (hiD.const_mul C)
  have hS : (∫ x, S x ∂μ) + ε ≤ η := by
    have hlin : (∫ x, S x ∂μ) = τ*((∫ x,A x ∂μ)+(∫ x,Z x ∂μ))+C*(∫ x,D x ∂μ) := by
      have hAZ : Integrable (fun x => A x + Z x) μ := hA.add hZ
      unfold S
      rw [integral_add (hAZ.const_mul τ) (hiD.const_mul C), integral_const_mul,
        integral_const_mul, integral_add (show Integrable A μ from hA) (show Integrable Z μ from hZ)]
    have h4 : (∫ x,A x ∂μ) + (∫ x,Z x ∂μ) ≤ 4 := by linarith
    have bound := add_le_add (mul_le_mul_of_nonneg_left h4 hτ.le) (mul_le_mul_of_nonneg_left hd hC)
    rw [hlin]
    have hLcalc : C*(2*ε/w) + ε = ε*L := by dsimp [L]; ring
    dsimp [τ] at bound ⊢
    linarith
  have both (t : ℝ) (ht : t ∈ Set.Icc a c) :
      Integrable (fun x => |F x-I x|^t) μ ∧ (∫ x, |F x-I x|^t ∂μ) ≤ η ∧
      Integrable (fun x => |Z x-I x|) μ ∧ (∫ x, |Z x-I x| ∂μ) + ε ≤ η := by
    have he (x : X) : |F x-I x|^t + |Z x-I x| ≤ S x := by
      rw [iEq]; exact control (F x) (hn x) t ht.1 ht.2
    have mn : Measurable (fun x => |F x-I x| ^ t) := (continuous_abs.measurable.comp (hF.sub mI)).pow_const _
    have mn' : Measurable (fun x => |Z x-I x|) := continuous_abs.measurable.comp ((hF.pow_const c).sub mI)
    have hx (x : X) : 0 ≤ |F x-I x| ^ t := Real.rpow_nonneg (abs_nonneg _) _
    have hu (x : X) : |F x-I x| ^ t ≤ S x := (le_add_of_nonneg_right (abs_nonneg _)).trans (he x)
    have hv (x : X) : |Z x-I x| ≤ S x := (le_add_of_nonneg_left (hx x)).trans (he x)
    have hi := hiS.mono' mn.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs,abs_of_nonneg (hx x)] using hu x)
    have hi' := hiS.mono' mn'.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hv x)
    exact ⟨hi,(integral_mono hi hiS hu).trans (by linarith),hi',by linarith [integral_mono hi' hiS hv]⟩
  have ⟨_,_,hiV,hV⟩ := both a ⟨le_rfl,hac.le⟩
  have hint : Integrable I μ := by
    apply (hZ.add hiV).mono' mI.aestronglyMeasurable
    filter_upwards with x
    change ‖I x‖ ≤ Z x + |Z x - I x|
    have hnI : 0 ≤ I x := by rw [iEq]; split <;> norm_num
    rw [Real.norm_eq_abs,abs_of_nonneg hnI]
    linarith [neg_abs_le (Z x - I x)]
  have hfin : μ E < ⊤ := by
    have on : IntegrableOn (fun _ : X => (1 : ℝ)) E μ := (integrable_indicator_iff hE).mp hint
    simpa using ((integrableOn_const_iff (C := (1:ℝ))).mp on)
  have hvol : |μ.real E - 1| ≤ η := by
    have hsmall : |(∫ x,Z x ∂μ) - μ.real E| ≤ ∫ x, |Z x - I x| ∂μ := by
      have hz := abs_integral_le_integral_abs (μ := μ) (f := fun x => Z x-I x)
      rw [integral_sub hZ hint] at hz
      simpa [I,integral_indicator_one hE] using hz
    calc
      |μ.real E-1| ≤ |μ.real E - (∫ x,Z x ∂μ)| + |(∫ x,Z x ∂μ)-1| := abs_sub_le ..
      _ ≤ η := by rw [abs_sub_comm (μ.real E)]; linarith
  exact ⟨hE,hfin,hvol,fun t ht => ⟨(both t ht).1,(both t ht).2.1⟩⟩

end LpGowers
