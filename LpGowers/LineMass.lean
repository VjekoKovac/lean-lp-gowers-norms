module

public import LpGowers.Euclidean
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! A positive integrable density cannot satisfy the midpoint inequality on
every line parallel to a fixed nonzero direction. Integrating against a slab
in one transverse coordinate bounds all translates by their common total mass. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace LpGowers

/-- Integrating over translations of a unit slab counts each point with
the same finite weight `1/|v j|`. -/
private theorem translated_slab_mass {n : ℕ} (F : Rn n → ℝ≥0∞) (hF : Measurable F)
    (j : Fin n) (v : Rn n) (hv : v j ≠ 0) :
    (∫⁻ t : ℝ, ∫⁻ x : Rn n, F (x+t • v) *
      (Set.Ioo (0:ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (x j)) =
    (∫⁻ x, F x) * ENNReal.ofReal |(v j)⁻¹| := by
  let w := (Set.Ioo (0:ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)
  have hw : Measurable w := measurable_const.indicator measurableSet_Ioo
  have mass (x : Rn n) : (∫⁻t : ℝ, w ((x-t•v) j)) = ENNReal.ofReal |(v j)⁻¹| := by
    let T := fun t : ℝ => (-v j)*t
    have hT : Measurable T := measurable_const.mul measurable_id
    have he (t : ℝ) : (x-t•v) j = T t+x j := by dsimp [T]; ring
    simp_rw [he]
    have hm : Measurable (fun y : ℝ => w (y+x j)) := hw.comp (measurable_id.add_const (x j))
    rw [← lintegral_map hm hT]
    change (∫⁻ y, w (y+x j) ∂Measure.map (fun t : ℝ => -v j*t) volume) = _
    rw [Real.map_volume_mul_left (neg_ne_zero.mpr hv),lintegral_smul_measure,
      lintegral_add_right_eq_self]
    simp [w,lintegral_indicator measurableSet_Ioo,Real.volume_Ioo]
  have shift (t : ℝ) : (∫⁻ x : Rn n, F (x+t•v)*w (x j)) = ∫⁻x : Rn n, F x*w ((x-t•v) j) := by
    simpa only [add_sub_cancel_right] using
      (lintegral_add_right_eq_self (μ:=volume) (fun x : Rn n => F x*w ((x-t•v) j)) (t•v))
  change (∫⁻t : ℝ, ∫⁻x : Rn n, F (x+t•v)*w (x j)) = _
  simp_rw [shift]
  rw [lintegral_lintegral_swap]
  · have hg (x : Rn n) : Measurable (fun t : ℝ => w ((x-t•v) j)) :=
      hw.comp ((measurable_pi_apply j).comp (measurable_const.sub (measurable_id.smul measurable_const)))
    simp_rw [lintegral_const_mul _ (hg _),mass]
    exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  · apply Measurable.aemeasurable
    exact (hF.comp measurable_snd).mul (hw.comp <| (measurable_pi_apply j).comp
      (measurable_snd.sub (measurable_fst.smul measurable_const)))

/-- Every nonzero direction admits a strict failure of the midpoint
upper bound for any positive density with finite integral. -/
theorem finite_mass_not_line_subharmonic {n : ℕ} (F : Rn n → ℝ≥0∞)
    (hf : Measurable F) (hpos : ∀ x, 0<F x) (hfin : (∫⁻x,F x) ≠ ⊤)
    (v : Rn n) (hv : v≠0) :
    ¬ ∀ (x : Rn n) (t : ℝ), F x ≤ F (x+t•v)+F (x+t•(-v)) := by
  intro H
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by contrapose! hv; ext j; exact hv j
  let w := (Set.Ioo (0:ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)
  let A := ∫⁻ x : Rn n, F x*w (x j)
  have hw : Measurable w := measurable_const.indicator measurableSet_Ioo
  have hA : 0<A := by
    apply (lintegral_pos_iff_support (hf.mul (hw.comp (measurable_pi_apply j)))).2
    let S := (fun x : Rn n => x j) ⁻¹' Set.Ioo (0:ℝ) 1
    have hS : IsOpen S := isOpen_Ioo.preimage (continuous_apply j)
    have hS' : S.Nonempty := ⟨fun _ => 1/2,by constructor <;> norm_num⟩
    apply (hS.measure_pos volume hS').trans_le (measure_mono ?_)
    intro x hx
    have hx' : x j ∈ Set.Ioo (0:ℝ) 1 := hx
    simpa [Function.mem_support,w,hx'] using (hpos x).ne'
  let J := fun (u : Rn n) (t : ℝ) => ∫⁻x : Rn n, F (x+t•u)*w (x j)
  have m (u : Rn n) : Measurable (J u) := by
    apply Measurable.lintegral_prod_right' (f := fun z : ℝ × Rn n => F (z.2+z.1•u)*w (z.2 j))
    exact (hf.comp (measurable_snd.add (measurable_fst.smul measurable_const))).mul
      (hw.comp ((measurable_pi_apply j).comp measurable_snd))
  have eq (u : Rn n) (hu : u j≠0) : (∫⁻ t, J u t) = (∫⁻x,F x)*ENNReal.ofReal |(u j)⁻¹| :=
    translated_slab_mass F hf j u hu
  have Ht (t : ℝ) : A ≤ J v t + J (-v) t := by
    rw [← lintegral_add_left (show Measurable (fun x : Rn n => F (x+t•v)*w (x j)) from
      (hf.comp (measurable_id.add_const _)).mul (hw.comp (measurable_pi_apply j)))]
    exact lintegral_mono fun x => (mul_le_mul_left (H x t) _).trans_eq (add_mul ..)
  have hI := lintegral_mono (μ:=volume) Ht
  rw [lintegral_const,Real.volume_univ,ENNReal.mul_top hA.ne',lintegral_add_left (m v),
    eq v hj, eq (-v) (neg_ne_zero.mpr hj)] at hI
  exact (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top⟩) (top_le_iff.mp hI)

end LpGowers
