module

public import LpGowers.ReverseDegree
public import LpGowers.TensorTransfer
public import LpGowers.ExtendedHolder

/-! # Normalized densities in degree-lowering stability

The autocorrelation norm assumptions make each normalizing mass positive and
finite. This module records the normalization and the simultaneous tensor
transfer used in the last paragraph of Section 5. -/

public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

/-- Normalized density from the `p`th moment of `F`. -/
@[expose] def momentDensity {X : Type*} [MeasurableSpace X] (ν : Measure X) (p : ℝ)
    (F : X → ℝ≥0∞) (x : X) : ℝ≥0∞ := (F x)^p / (∫⁻ y, F y ^ p ∂ν)

theorem momentDensity_measurable {X : Type*} [MeasurableSpace X] (ν : Measure X) (p : ℝ)
    {F : X → ℝ≥0∞} (hF : Measurable F) : Measurable (momentDensity ν p F) :=
  (hF.pow_const p).div_const _

theorem momentDensity_integral {X : Type*} [MeasurableSpace X] (ν : Measure X) (p : ℝ)
    {F : X → ℝ≥0∞} (hF : Measurable F) (h0 : (∫⁻ x, F x ^ p ∂ν) ≠ 0)
    (ht : (∫⁻ x, F x ^ p ∂ν) ≠ ⊤) : (∫⁻ x, momentDensity ν p F x ∂ν) = 1 := by
  simp only [momentDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ (hF.pow_const p), ENNReal.mul_inv_cancel h0 ht]

/-- The `L¹` distance of equally rescaled densities. -/
theorem l1DensityError_scale {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {F G : X → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    l1DensityError ν (fun x => c * F x) (fun x => c * G x) = c * l1DensityError ν F G := by
  unfold l1DensityError
  have h (x : X) : (c*F x-c*G x)+(c*G x-c*F x) = c*((F x-G x)+(G x-F x)) := by
    rw [mul_add, ENNReal.mul_sub (fun _ _ => hc), ENNReal.mul_sub (fun _ _ => hc)]
  simp only [h]
  exact lintegral_const_mul c ((hF.sub hG).add (hG.sub hF))

/-- Rescaling an approximation to the normalized moment gives the corresponding
relative-error inequality in the source. -/
theorem unnormalize_l1 {X : Type*} [MeasurableSpace X] (ν : Measure X) (p : ℝ)
    {F G : X → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) (hp : 0 < p)
    (h0 : (∫⁻ x, F x ^ p ∂ν) ≠ 0) (ht : (∫⁻ x, F x ^ p ∂ν) ≠ ⊤)
    (δ : ℝ≥0∞) (h : l1DensityError ν (momentDensity ν p F) G ≤ δ) :
    l1DensityError ν (fun x => F x ^ p) (fun x => (lp ν p F)^p * G x) ≤ δ*(lp ν p F)^p := by
  let A := ∫⁻ x, F x ^ p ∂ν
  have hA : (lp ν p F)^p = A := by simp [lp, ← ENNReal.rpow_mul, hp.ne', A]
  have hpoint : (fun x => A * momentDensity ν p F x) = fun x => F x ^ p := by
    funext x
    exact ENNReal.mul_div_cancel h0 ht
  rw [hA, ← hpoint, l1DensityError_scale ν (momentDensity_measurable ν p hF) hG A ht, mul_comm δ]
  exact mul_le_mul_right h A

/-- The final reduction in Section 5. Approximate the normalized joint power
by the Loomis–Whitney product and approximate all of its normalized faces by
the same one-dimensional factors. The masses in the conclusion are exact. -/
theorem degreeApproximation_of_normalized_densities {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    (j : ℕ) {p : ℝ} (hp : 0 < p) {q : Fin (j+2) → ℝ} (hq : ∀ i, 0 < q i)
    {f : G → ℝ≥0} (hf : AEMeasurable f μ)
    (hJ : 0 < gowers μ (j+2) p f ∧ gowers μ (j+2) p f < ⊤)
    (hI : ∀ i, 0 < gowers μ (j+1) (q i) f ∧ gowers μ (j+1) (q i) f < ⊤)
    (r : Fin (j+2) → G → ℝ≥0) (hr : ∀ i, Measurable (r i) ∧ (∫⁻ x, (r i x : ℝ≥0∞) ∂μ) = 1)
    (δ ε : ℝ≥0∞) {η : ℝ} (hδ : δ ≤ ENNReal.ofReal η)
    (hε : ε + 2*(j+2:ℕ)*δ^(1/((j:ℝ)+1)) ≤ ENNReal.ofReal η)
    (hjoint : l1DensityError (cubeMeasure μ (j+2))
      (momentDensity (cubeMeasure μ (j+2)) p (autocorrelation μ (j+2) f))
      (lwProduct j (fun i => momentDensity (cubeMeasure μ (j+1)) (q i) (autocorrelation μ (j+1) f))) ≤ ε)
    (hface : ∀ i, l1DensityError (cubeMeasure μ (j+1))
      (momentDensity (cubeMeasure μ (j+1)) (q i) (autocorrelation μ (j+1) f))
      (fun y => ∏ t, (r (i.succAbove t) (y t) : ℝ≥0∞)) ≤ δ) :
    DegreeApproximation μ (j+1) p q f η := by
  let M := autocorrelation μ (j+1) f
  let F := autocorrelation μ (j+2) f
  let V := fun i => momentDensity (cubeMeasure μ (j+1)) (q i) M
  let W := momentDensity (cubeMeasure μ (j+2)) p F
  let A := fun (i : Fin (j+2)) (y : Fin (j+1) → G) => ∏ t, (r (i.succAbove t) (y t) : ℝ≥0∞)
  have hm : Measurable M := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hF : Measurable F := measurable_autocorrelation_of_aemeasurable μ _ hf
  have hv i : Measurable (V i) := momentDensity_measurable _ _ hm
  have hw : Measurable W := momentDensity_measurable _ _ hF
  have hA i : Measurable (A i) := Finset.measurable_prod _ (fun t _ =>
    (measurable_coe_nnreal_ennreal.comp (hr (i.succAbove t)).1).comp (measurable_pi_apply t))
  have hR : Measurable (fun x : Fin (j+2) → G => ∏ i, (r i (x i) : ℝ≥0∞)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_coe_nnreal_ennreal.comp (hr i).1).comp (measurable_pi_apply i))
  have reg (d : ℕ) {s : ℝ} (hs : 0 < s) (h : 0 < gowers μ d s f ∧ gowers μ d s f < ⊤) :
      let L := ∫⁻ x, (autocorrelation μ d f x)^s ∂cubeMeasure μ d
      L ≠ 0 ∧ L ≠ ⊤ := by
    intro L
    have he : 0 < (1/s)*(1/(2:ℝ)^d) := by positivity
    change 0 < (L ^ (1/s)) ^ (1/(2:ℝ)^d) ∧ (L ^ (1/s)) ^ (1/(2:ℝ)^d) < ⊤ at h
    rw [← ENNReal.rpow_mul, ENNReal.rpow_lt_top_iff_of_pos he] at h
    exact ⟨fun ez => h.1.ne' ((ENNReal.rpow_eq_zero_iff_of_pos he).mpr ez),h.2.ne⟩
  have v1 i : (∫⁻ y, V i y ∂cubeMeasure μ (j+1)) = 1 :=
    momentDensity_integral _ _ hm (reg _ (hq i) (hI i)).1 (reg _ (hq i) (hI i)).2
  have a1 i : (∫⁻ y, A i y ∂cubeMeasure μ (j+1)) = 1 := by
    simpa only [A,hr,Finset.prod_const_one] using
      lintegral_pi_separated μ (j+1) (fun t y => (r (i.succAbove t) y : ℝ≥0∞))
        (fun t => measurable_coe_nnreal_ennreal.comp (hr (i.succAbove t)).1)
  have prod := lw_product_transfer μ hv hA (fun i => (v1 i).le) (fun i => (a1 i).le) hface
  have hprod : lwProduct j A = fun x => ∏ i, (r i (x i) : ℝ≥0∞) := lwProduct_face_tensors j (fun i x => (r i x : ℝ≥0∞))
  rw [hprod] at prod
  refine ⟨r,hr,?_,?_⟩
  · apply unnormalize_l1 _ p hF hR hp (reg _ hp hJ).1 (reg _ hp hJ).2
    exact (l1DensityError_triangle _ hw (lwProduct_measurable hv) hR).trans
      ((add_le_add hjoint prod).trans hε)
  · intro i
    exact unnormalize_l1 _ (q i) hm (hA i) (hq i) (reg _ (hq i) (hI i)).1
      (reg _ (hq i) (hI i)).2 _ ((hface i).trans hδ)

/-- A deficit in a positive power is uniformly small when the multiplicative
deficit is small. This gives the epsilon thresholds in Section 5. -/
theorem small_power_deficit (t : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
      ENNReal.ofReal (1-η) ≤ (ENNReal.ofReal (1-ε))^t := by
  have hcont : ContinuousAt (fun ε : ℝ => (1-ε)^t) 0 :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))
  have h := (Metric.continuousAt_iff.mp hcont) η hη
  obtain ⟨δ,hδ,H⟩ := h
  refine ⟨min δ (1/2),lt_min hδ (by norm_num),min_le_of_right_le (by norm_num),?_⟩
  intro ε he hε
  have hε' : ε < δ := hε.trans_le (min_le_left _ _)
  have he1 : 0 < 1-ε := by have := hε.trans_le (min_le_right _ _); linarith
  have he' := H (show dist ε 0 < δ by simpa [Real.dist_eq,abs_of_nonneg he] using hε')
  simp [Real.dist_eq] at he'
  have he'' : 1-η ≤ (1-ε)^t := by linarith only [(abs_lt.mp he').1]
  rw [ENNReal.ofReal_rpow_of_pos he1]
  exact ENNReal.ofReal_le_ofReal he''

/-- Passing to moments clears both outer Gowers-normalization powers exactly. -/
theorem degree_moment_conversion {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (k : ℕ) {p : ℝ} (hp : 0 < p) (q θ : Fin (k+1) → ℝ) (hq : ∀ i, 0 < q i)
    (f : G → ℝ≥0) :
    let t := (2:ℝ)^(k+1)*p
    (gowers μ (k+1) p f)^t = (∫⁻ x, (autocorrelation μ (k+1) f x)^p ∂cubeMeasure μ (k+1)) ∧
    (lowerProduct μ k q θ f)^t =
      ∏ i, (∫⁻ y, (autocorrelation μ k f y)^(q i) ∂cubeMeasure μ k) ^ (2*p*θ i/q i) := by
  intro t
  have ht : 0 ≤ t := by dsimp [t]; positivity
  constructor
  · simp only [gowers,lp,← ENNReal.rpow_mul]
    rw [show (1/p)*(1/(2:ℝ)^(k+1))*t = 1 by dsimp [t]; field_simp, ENNReal.rpow_one]
  · unfold lowerProduct
    rw [← ENNReal.prod_rpow_of_nonneg ht]
    apply Finset.prod_congr rfl
    intro i _
    simp only [gowers,lp,← ENNReal.rpow_mul]
    congr 1
    dsimp [t]
    rw [pow_succ]
    field_simp [(hq i).ne']

/-- Mass deficit control is enough to compare a subnormalized geometric
mean with its normalization in `L¹`. -/
theorem l1DensityError_small_scaling {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {W : X → ℝ≥0∞} (hm : Measurable W) (hW : (∫⁻ x,W x ∂ν)=1)
    {D : ℝ≥0∞} (hD : D ≤ 1) :
    l1DensityError ν (fun x => D*W x) W = 1-D := by
  have hle (x : X) : D*W x ≤ W x := by simpa using mul_le_mul_left hD (W x)
  unfold l1DensityError
  simp only [tsub_eq_zero_of_le (hle _),zero_add]
  have hfin : (∫⁻ x,W x ∂ν) ≠ ⊤ := by simp [hW]
  calc
    _ = ∫⁻ x,(1-D)*W x ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_lt_top hm hfin] with x hx
      simp only [ENNReal.sub_mul (fun _ _ => hx.ne),one_mul]
    _ = _ := by rw [lintegral_const_mul _ hm,hW,mul_one]

/-- If two probability densities are close, their masses differ by at most
the same `L¹` error. The second density may have mass below one. -/
theorem one_sub_lintegral_le_l1 {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {W V : X → ℝ≥0∞} (_hm : Measurable W) (hv : Measurable V) (hW : (∫⁻ x,W x ∂ν)=1) :
    1-(∫⁻ x,V x ∂ν) ≤ l1DensityError ν W V := by
  rw [← hW]
  exact (lintegral_sub_le V W hv).trans (lintegral_mono (fun _ => le_add_right (le_refl _)))

/-- Distance from the normalized high-order moment to the product of its normalized faces. -/
@[expose] def jointFaceError {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (j : ℕ) (p : ℝ) (q : Fin (j+2) → ℝ) (f : G → ℝ≥0) : ℝ≥0∞ :=
  l1DensityError (cubeMeasure μ (j+2))
    (momentDensity (cubeMeasure μ (j+2)) p (autocorrelation μ (j+2) f))
    (lwProduct j (fun i => momentDensity (cubeMeasure μ (j+1)) (q i) (autocorrelation μ (j+1) f)))

/-- A finite positive Gowers functional has a finite positive underlying moment. -/
theorem moment_regular_of_gowers {G : Type*} [MeasurableSpace G] [AddCommMonoid G]
    (μ : Measure G) (d : ℕ) {p : ℝ} (hp : 0 < p) {f : G → ℝ≥0}
    (h : 0 < gowers μ d p f ∧ gowers μ d p f < ⊤) :
    let L := ∫⁻ x, (autocorrelation μ d f x)^p ∂cubeMeasure μ d
    L ≠ 0 ∧ L ≠ ⊤ := by
  intro L
  have he : 0 < (1/p)*(1/(2:ℝ)^d) := by positivity
  change 0 < (L ^ (1/p)) ^ (1/(2:ℝ)^d) ∧ (L ^ (1/p)) ^ (1/(2:ℝ)^d) < ⊤ at h
  rw [← ENNReal.rpow_mul, ENNReal.rpow_lt_top_iff_of_pos he] at h
  exact ⟨fun ez => h.1.ne' ((ENNReal.rpow_eq_zero_iff_of_pos he).mpr ez),h.2.ne⟩

theorem l1DensityError_congr_ae {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {A B A' B' : X → ℝ≥0∞} (ha : A =ᵐ[ν] A') (hb : B =ᵐ[ν] B') :
    l1DensityError ν A B = l1DensityError ν A' B' := by
  apply lintegral_congr_ae
  filter_upwards [ha,hb] with x hx hy
  rw [hx,hy]

theorem l1DensityError_comm {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (A B : X → ℝ≥0∞) : l1DensityError ν A B = l1DensityError ν B A :=
  lintegral_congr (fun _ => add_comm _ _)

end LpGowers
