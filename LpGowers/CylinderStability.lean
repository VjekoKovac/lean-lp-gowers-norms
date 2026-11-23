module

public import LpGowers.CylinderBox
import Mathlib.Tactic

/-! # Geometric Loomis–Whitney near-extremizers

Lemma 6.1 follows by applying the functional stability theorem to the
normalized indicators of the faces, followed by the fibre-selection argument. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators symmDiff
namespace LpGowers

/-- Lemma 5.2 also approximates the product on the full cube. This follows
from the telescoping estimate for perturbing all faces simultaneously. -/
theorem lw_joint_stability (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (f : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞),
    (∀ i, Measurable (f i)) → (∀ i, (∫⁻ y, f i y ∂cubeMeasure μ (k+1)) = 1) →
    ENNReal.ofReal (1-ε) ≤ ∫⁻ x, lwProduct k f x ∂cubeMeasure μ (k+2) →
    ∃ r : Fin (k+2) → X → ℝ≥0∞, (∀ i, Measurable (r i) ∧ (∫⁻ y, r i y ∂μ) = 1) ∧
      l1DensityError (cubeMeasure μ (k+2)) (lwProduct k f)
        (fun x => ∏ i, r i (x i)) ≤ ENNReal.ofReal η := by
  let t := 1/((k:ℝ)+1)
  let m := ((k+2:ℕ):ℝ)
  let b := η/(2*m)
  have ht : 0 < t := by dsimp [t]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨δ,hd,H⟩ := lw_stability_ennreal k (Real.rpow_pos_of_pos hb t⁻¹)
  refine ⟨δ,hd,?_⟩
  intro ε he heδ X _ μ _ f hf hn hp
  obtain ⟨r,hr,HE⟩ := H ε he heδ μ f hf hn hp
  let T := fun (i : Fin (k+2)) (y : Fin (k+1) → X) => ∏ j, r (i.succAbove j) (y j)
  have hTm (i) : Measurable (T i) :=
    Finset.measurable_prod _ (fun j _ => (hr _).1.comp (measurable_pi_apply j))
  have hTn (i) : (∫⁻ y, T i y ∂cubeMeasure μ (k+1)) = 1 := by
    simpa only [T,(fun j => (hr j).2),Finset.prod_const_one] using
      lintegral_pi_separated μ (k+1) (fun j => r (i.succAbove j)) (fun j => (hr _).1)
  have Ht := lw_product_transfer μ hf hTm (fun i => (hn i).le) (fun i => (hTn i).le) HE
  rw [show lwProduct k T = fun x => ∏ i, r i (x i) from lwProduct_face_tensors k r] at Ht
  refine ⟨r,hr,Ht.trans_eq ?_⟩
  change 2*(k+2:ℕ)*(ENNReal.ofReal (b^t⁻¹))^t = _
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hb.le _) ht.le, Real.rpow_inv_rpow hb.le ht.ne']
  have hreal : 2*m*b = η := by dsimp [b]; field_simp
  have HH := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*m), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)] at HH
  simpa only [m, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using HH

/-- Cylinder intersection in the geometric Loomis–Whitney inequality. -/
def cylinderIntersection {X : Type*} {k : ℕ} (E : Fin (k+2) → Set (Fin (k+1) → X)) :
    Set (Fin (k+2) → X) := {x | ∀ i, deleteCoord i x ∈ E i}

/-- Lemma 6.1. A near extremal intersection of finite, positive-measure
cylinders is close in relative symmetric difference to a product of measurable
one-coordinate sets of finite, positive measure. -/
theorem cylinder_stability (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
      (E : Fin (k+2) → Set (Fin (k+1) → X)),
    (∀ i, MeasurableSet (E i) ∧ (cubeMeasure μ (k+1)) (E i) ≠ 0 ∧ (cubeMeasure μ (k+1)) (E i) ≠ ⊤) →
    ENNReal.ofReal (1-ε) * (∏ i, (cubeMeasure μ (k+1)) (E i)) ^ (1/((k:ℝ)+1)) ≤
      (cubeMeasure μ (k+2)) (cylinderIntersection E) →
    ∃ A : Fin (k+2) → Set X, (∀ i, MeasurableSet (A i) ∧ μ (A i) ≠ 0 ∧ μ (A i) ≠ ⊤) ∧
      (cubeMeasure μ (k+2)).real (cylinderIntersection E ∆ Set.univ.pi A) ≤
        η * (cubeMeasure μ (k+2)).real (cylinderIntersection E) := by
  classical
  obtain ⟨d,hd,HB⟩ := box_of_uniform_tensor (k+1) hη
  obtain ⟨D,hD,HF⟩ := lw_joint_stability k (half_pos hd)
  let δ := min D (min (d/2) (1/2))
  have hδ : 0 < δ := lt_min hD (lt_min (half_pos hd) (by norm_num))
  refine ⟨δ,hδ,?_⟩
  intro ε he heδ X _ μ _ E hE hnear
  let ν := cubeMeasure μ (k+2)
  let ξ := cubeMeasure μ (k+1)
  let Ω := cylinderIntersection E
  let m := fun i => ξ (E i)
  let t := 1/((k:ℝ)+1)
  let M := (∏ i, m i)^t
  let f := fun i => (E i).indicator (fun _ => (m i)⁻¹)
  let W := Ω.indicator (fun _ => (ν Ω)⁻¹)
  let s := ν Ω / M
  have ht : 0 < t := by dsimp [t]; positivity
  have hm : (∏ i, m i) ≠ 0 ∧ (∏ i, m i) ≠ ⊤ :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hE i).2.1, ENNReal.prod_ne_top fun i _ => (hE i).2.2⟩
  have hM0 : M ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hm.1) hm.2).ne'
  have hMt : M ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hm.1 hm.2
  have hΩm : MeasurableSet Ω := by
    rw [show Ω = ⋂ i, (deleteCoord i) ⁻¹' E i by ext x; simp [Ω,cylinderIntersection]]
    exact MeasurableSet.iInter (fun i => (measurable_omitCoord i) (hE i).1)
  have hf i : Measurable (f i) := measurable_const.indicator (hE i).1
  have hn i : (∫⁻ y, f i y ∂ξ) = 1 := by
    rw [show (∫⁻ y, f i y ∂ξ) = (m i)⁻¹*m i from lintegral_indicator_const (hE i).1 _]
    exact ENNReal.inv_mul_cancel (hE i).2.1 (hE i).2.2
  have prodEq : lwProduct k f = Ω.indicator (fun _ => M⁻¹) := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
      have hin : ∀ i, deleteCoord i x ∈ E i := hx
      simp only [lwProduct, f, Set.indicator_of_mem (hin _)]
      change (∏ i, (m i)⁻¹ ^ t) = ((∏ i, m i) ^ t)⁻¹
      simp only [ENNReal.inv_rpow, ← ENNReal.prod_rpow_of_nonneg ht.le]
      exact (ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (ENNReal.rpow_ne_top_of_ne_zero
        (hE j).2.1 (hE j).2.2))).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i,hi⟩ : ∃ i, deleteCoord i x ∉ E i := by simpa only [Ω,cylinderIntersection,mem_ofPred_eq,not_forall] using hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change ((E i).indicator (fun _ => (m i)⁻¹) (deleteCoord i x))^t = _
      rw [Set.indicator_of_notMem hi, ENNReal.zero_rpow_of_pos ht]
  have Ieq : (∫⁻ x, lwProduct k f x ∂ν) = s := by
    rw [prodEq, lintegral_indicator_const hΩm]; exact mul_comm _ _
  have hle : s ≤ 1 := by
    rw [← Ieq]
    exact (functionalLoomisWhitney μ k f hf).trans (by simp [hn,ξ] at *)
  have hlo : ENNReal.ofReal (1-ε) ≤ s :=
    (ENNReal.le_div_iff_mul_le (Or.inl hM0) (Or.inl hMt)).mpr hnear
  have he1 : ε < 1 := heδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num : (1/2:ℝ) ≤ 1)))
  have hΩ0 : ν Ω ≠ 0 := fun ez => (ENNReal.ofReal_pos.mpr (sub_pos.mpr he1)).not_ge
    (by simpa [s,ez] using hlo)
  have hΩt : ν Ω ≠ ⊤ := ne_top_of_le_ne_top hMt (by
    have H := (ENNReal.div_le_iff_le_mul (Or.inl hM0) (Or.inl hMt)).mp hle
    simpa using H)
  obtain ⟨r,hr,HH⟩ := HF ε he (heδ.trans_le (min_le_left _ _)) μ f hf hn (hlo.trans_eq Ieq.symm)
  have hW : Measurable W := measurable_const.indicator hΩm
  have hWn : (∫⁻ x, W x ∂ν) = 1 := (lintegral_indicator_const hΩm _).trans (ENNReal.inv_mul_cancel hΩ0 hΩt)
  have hsW : (fun x => s * W x) = lwProduct k f := by
    rw [prodEq]
    funext x
    by_cases hx : x ∈ Ω
    · simp only [W,Set.indicator_of_mem hx,s,div_eq_mul_inv,mul_right_comm _ M⁻¹, ENNReal.mul_inv_cancel hΩ0 hΩt,one_mul]
    · simp [W,hx]
  have hE' : 1-s ≤ ENNReal.ofReal ε := by
    apply tsub_le_iff_left.mpr
    have HP := add_le_add_left hlo (ENNReal.ofReal ε)
    rw [← ENNReal.ofReal_add (sub_pos.mpr he1).le he, sub_add_cancel, ENNReal.ofReal_one] at HP
    exact HP
  apply HB μ Ω hΩm hΩ0 hΩt r (fun i => (hr i).1) (fun i => (hr i).2)
  have hR : Measurable (fun x : Fin (k+2) → X => ∏ i, r i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hr i).1.comp (measurable_pi_apply i))
  apply (l1DensityError_triangle ν hW (lwProduct_measurable hf) hR).trans
  have hWv : l1DensityError ν W (lwProduct k f) = 1-s := by
    rw [l1DensityError_comm, ← hsW]
    exact l1DensityError_small_scaling ν hW hWn hle
  rw [hWv]
  apply (add_le_add hE' HH).trans
  rw [← ENNReal.ofReal_add he (half_pos hd).le]
  apply ENNReal.ofReal_le_ofReal
  have H : ε ≤ d/2 := heδ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  linarith

end LpGowers
