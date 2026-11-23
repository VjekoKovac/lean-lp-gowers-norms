module

public import LpGowers.SymmetricLowering
public import LpGowers.ProductIntegral
public import Mathlib.Analysis.MeanInequalitiesPow

/-! # Perturbing Loomis–Whitney products

This supplies the telescoping estimate used after (5.8) in Kovač–Rogers.
All norms are computed with the product measures on the actual coordinate
deletion spaces. Nonnegative input densities can have infinite point values. -/

public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace LpGowers

private theorem directed_step {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {k : ℕ} {F G : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞}
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i)) (i : Fin (k+2))
    (he : ∀ t, t ≠ i → F t = G t)
    (hN : ∀ t, (∫⁻ y, F t y ∂cubeMeasure μ (k+1)) ≤ 1) :
    (∫⁻ x, lwProduct k F x - lwProduct k G x ∂cubeMeasure μ (k+2)) ≤
      (∫⁻ y, F i y - G i y ∂cubeMeasure μ (k+1)) ^ (1/((k:ℝ)+1)) := by
  classical
  let r := 1/((k:ℝ)+1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_iff₀ (by positivity)).2; simp
  let D := fun t y => if t=i then F t y - G t y else F t y
  have hD (t) : Measurable (D t) := by
    by_cases h : t=i
    · subst t
      simp only [D,ite_true]
      fun_prop (disch := solve_by_elim)
    · simpa only [D,ite_eq_right h] using hF t
  have hpt (x) : lwProduct k F x - lwProduct k G x ≤ lwProduct k D x := by
    let u := fun t => F t (deleteCoord t x) ^ r
    let v := fun t => G t (deleteCoord t x) ^ r
    let e := fun t => D t (deleteCoord t x) ^ r
    change (∏ t, u t) - (∏ t, v t) ≤ ∏ t, e t
    let s := Finset.univ.erase i
    have hv : (∏ t ∈ s, v t) = ∏ t ∈ s, u t := Finset.prod_congr rfl
      (fun t ht => by simp [v,u,he t (Finset.ne_of_mem_erase ht)])
    have hd : (∏ t ∈ s, e t) = ∏ t ∈ s, u t := Finset.prod_congr rfl
      (fun t ht => by simp [e,u,D,Finset.ne_of_mem_erase ht])
    rw [← Finset.mul_prod_erase _ u (Finset.mem_univ i), ← Finset.mul_prod_erase _ v (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ e (Finset.mem_univ i)]
    change u i * (∏ t ∈ s, u t) - v i * (∏ t ∈ s, v t) ≤ e i * (∏ t ∈ s, e t)
    rw [hv,hd,tsub_le_iff_left,← add_mul]
    apply mul_le_mul_left
    have huz : F i (deleteCoord i x) ≤ G i (deleteCoord i x) + (F i (deleteCoord i x)-G i (deleteCoord i x)) := le_add_tsub
    dsimp only [u,v,e,D]
    simp only [ite_true]
    exact (ENNReal.rpow_le_rpow huz hr).trans (ENNReal.rpow_add_le_add_rpow _ _ hr hr1)
  have hlw := functionalLoomisWhitney μ k D hD
  calc
    _ ≤ _ := lintegral_mono hpt
    _ ≤ _ := hlw
    _ ≤ _ := by
      let I := fun t => (∫⁻ y, D t y ∂cubeMeasure μ (k+1)) ^ r
      change (∏ t, I t) ≤ _
      rw [← Finset.mul_prod_erase _ I (Finset.mem_univ i)]
      have htail : (∏ t ∈ Finset.univ.erase i, I t) ≤ 1 := Finset.prod_le_one
        fun t ht => by
          dsimp only [I,D]
          simp only [ite_eq_right (Finset.ne_of_mem_erase ht)]
          simpa using ENNReal.rpow_le_rpow (hN t) hr
      calc
        _ ≤ I i * 1 := mul_le_mul_right htail _
        _ = _ := by simp [I,D,r]

private theorem directed_triangle (a b c : ℝ≥0∞) : a-c ≤ (a-b)+(b-c) := by
  apply tsub_le_iff_left.mpr
  calc
    a ≤ b+(a-b) := le_add_tsub
    _ ≤ (c+(b-c))+(a-b) := add_le_add_left le_add_tsub _
    _ = _ := by ac_rfl

private theorem directed_lw_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {k : ℕ} {F G : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞}
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (hfN : ∀ i, (∫⁻ y, F i y ∂cubeMeasure μ (k+1)) ≤ 1)
    (hgN : ∀ i, (∫⁻ y, G i y ∂cubeMeasure μ (k+1)) ≤ 1)
    {δ : ℝ≥0∞} (hδ : ∀ i, (∫⁻ y, F i y - G i y ∂cubeMeasure μ (k+1)) ≤ δ) :
    (∫⁻ x, lwProduct k F x - lwProduct k G x ∂cubeMeasure μ (k+2)) ≤
      (k+2:ℕ) * δ ^ (1/((k:ℝ)+1)) := by
  classical
  let H := fun (t : ℕ) (i : Fin (k+2)) => if i.val < t then G i else F i
  let r := 1/((k:ℝ)+1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hm (t i) : Measurable (H t i) := by by_cases h : i.val < t <;> simp [H,h,hF,hG]
  have hN (t i) : (∫⁻ y, H t i y ∂cubeMeasure μ (k+1)) ≤ 1 := by
    by_cases h : i.val < t <;> simp [H,h,hfN,hgN]
  have step (t : ℕ) (ht : t < k+2) :
      (∫⁻ x, lwProduct k (H t) x - lwProduct k (H (t+1)) x ∂cubeMeasure μ (k+2)) ≤ δ ^ r := by
    let i : Fin (k+2) := ⟨t,ht⟩
    have hrest (v : Fin (k+2)) (hv : v ≠ i) : H t v = H (t+1) v := by
      have hne : v.val ≠ t := fun e => hv (Fin.ext e)
      have hiff : v.val < t ↔ v.val < t+1 := by omega
      simp only [H,hiff]
    apply (directed_step μ (hm t) (hm (t+1)) i hrest (hN t)).trans
    apply ENNReal.rpow_le_rpow _ hr
    simpa [i,H] using hδ i
  have total (t : ℕ) (ht : t ≤ k+2) :
      (∫⁻ x, lwProduct k (H 0) x - lwProduct k (H t) x ∂cubeMeasure μ (k+2)) ≤ t * δ ^ r := by
    induction t with
    | zero => simp
    | succ t ih =>
      calc
        _ ≤ ∫⁻ x, (lwProduct k (H 0) x - lwProduct k (H t) x) +
            (lwProduct k (H t) x - lwProduct k (H (t+1)) x) ∂cubeMeasure μ (k+2) :=
          lintegral_mono (fun x => directed_triangle _ _ _)
        _ = _ := lintegral_add_left ((lwProduct_measurable (hm 0)).sub (lwProduct_measurable (hm t))) _
        _ ≤ _ := add_le_add (ih (by omega)) (step t (by omega))
        _ = _ := by push_cast; ring
  have h₀ : H 0 = F := by funext i; simp [H]
  have hend : H (k+2) = G := by funext i; simp [H,i.isLt]
  simpa only [h₀,hend,r] using total (k+2) (le_refl _)

/-- Simultaneous `L¹` control of the global product from perturbations of
all codimension-one densities. This is the telescoping estimate (5.9). -/
theorem lw_product_transfer {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {k : ℕ} {F G : Fin (k+2) → (Fin (k+1) → X) → ℝ≥0∞}
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (hfN : ∀ i, (∫⁻ y, F i y ∂cubeMeasure μ (k+1)) ≤ 1)
    (hgN : ∀ i, (∫⁻ y, G i y ∂cubeMeasure μ (k+1)) ≤ 1)
    {δ : ℝ≥0∞} (hδ : ∀ i, l1DensityError (cubeMeasure μ (k+1)) (F i) (G i) ≤ δ) :
    l1DensityError (cubeMeasure μ (k+2)) (lwProduct k F) (lwProduct k G) ≤
      2 * (k+2:ℕ) * δ ^ (1/((k:ℝ)+1)) := by
  let ν := cubeMeasure μ (k+1)
  have hfg (i) : (∫⁻ y, F i y - G i y ∂ν) ≤ δ :=
    (lintegral_mono (fun _ => le_add_right (le_refl _) )).trans (hδ i)
  have hgf (i) : (∫⁻ y, G i y - F i y ∂ν) ≤ δ :=
    (lintegral_mono (fun _ => le_add_left (le_refl _) )).trans (hδ i)
  unfold l1DensityError
  rw [lintegral_add_left (f := fun x => lwProduct k F x - lwProduct k G x) ((lwProduct_measurable hF).sub (lwProduct_measurable hG))]
  apply (add_le_add (directed_lw_bound μ hF hG hfN hgN hfg)
    (directed_lw_bound μ hG hF hgN hfN hgf)).trans_eq
  ring

/-- Multiplying the `(d−1)`st roots of all face tensor densities recovers the
full tensor density exactly. -/
theorem lwProduct_face_tensors {X : Type*} (k : ℕ) (r : Fin (k+2) → X → ℝ≥0∞) :
    lwProduct k (fun i y => ∏ j : Fin (k+1), r (i.succAbove j) (y j)) =
      fun x => ∏ i, r i (x i) := by
  classical
  funext x
  let h := fun i => r i (x i)
  let s := 1/((k:ℝ)+1)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hface (i : Fin (k+2)) : (∏ j : Fin (k+1), h (i.succAbove j)) =
      ∏ j, (if j=i then 1 else h j) := by
    rw [Fin.prod_univ_succAbove (fun j => if j=i then 1 else h j) i]
    simp
  change (∏ i : Fin (k+2), (∏ j : Fin (k+1), h (i.succAbove j)) ^ s) = ∏ i, h i
  simp_rw [hface, ← ENNReal.prod_rpow_of_nonneg hs]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.prod_univ_succAbove _ i]
  simp only [ite_true, ENNReal.one_rpow, one_mul, Fin.ne_succAbove, ite_false, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp [s, show (k:ℝ)+1 ≠ 0 by positivity]

private theorem absDiff_mul (a b A B : ℝ≥0∞) :
    (a*A-b*B) + (b*B-a*A) ≤ ((a-b)+(b-a))*A + b*((A-B)+(B-A)) := by
  have sc (v x y : ℝ≥0∞) : v*x-v*y ≤ v*(x-y) := by
    apply tsub_le_iff_left.mpr
    rw [← mul_add]
    exact mul_le_mul_right le_add_tsub _
  have scr (v x y : ℝ≥0∞) : x*v-y*v ≤ (x-y)*v := by simpa only [mul_comm _ v] using sc v x y
  calc
    _ ≤ ((a*A-b*A)+(b*A-b*B))+((b*B-b*A)+(b*A-a*A)) :=
        add_le_add (directed_triangle _ _ _) (directed_triangle _ _ _)
    _ ≤ ((a-b)*A+b*(A-B))+(b*(B-A)+(b-a)*A) :=
        add_le_add (add_le_add (scr A a b) (sc b A B)) (add_le_add (sc b B A) (scr A b a))
    _ = _ := by rw [add_mul,mul_add]; ac_rfl

/-- Total variation in the `L¹` convention is subadditive under taking
products of probability densities. Each coordinate error is counted once. -/
theorem l1_product_densities_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (n : ℕ) (f g : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfm : ∀ i, (∫⁻ x, f i x ∂μ) = 1) (hgm : ∀ i, (∫⁻ x, g i x ∂μ) = 1) :
    l1DensityError (cubeMeasure μ n) (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) ≤
      ∑ i, l1DensityError μ (f i) (g i) := by
  induction n with
  | zero => simp [l1DensityError]
  | succ n ih =>
    let A := fun y : Fin n → X => ∏ i, f i.succ (y i)
    let B := fun y : Fin n → X => ∏ i, g i.succ (y i)
    have hA : Measurable A := Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
    have hB : Measurable B := Finset.measurable_prod _ (fun i _ => (hg i.succ).comp (measurable_pi_apply i))
    have hmA : (∫⁻ y, A y ∂cubeMeasure μ n) = 1 := by
      simpa only [A,hfm,Finset.prod_const_one] using
        lintegral_pi_separated μ n (fun i => f i.succ) (fun i => hf i.succ)
    let D := fun y => (A y-B y)+(B y-A y)
    let d := fun x => (f 0 x-g 0 x)+(g 0 x-f 0 x)
    have hd : Measurable d := ((hf 0).sub (hg 0)).add ((hg 0).sub (hf 0))
    have hD : Measurable D := (hA.sub hB).add (hB.sub hA)
    have hF : Measurable (fun x : Fin (n+1) → X => ∏ i, f i (x i)) :=
      Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
    have hG : Measurable (fun x : Fin (n+1) → X => ∏ i, g i (x i)) :=
      Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
    have e (a : X) (y : Fin n → X) :
        (∏ i, f i ((Fin.cons (α := fun _ => X) a y) i)) = f 0 a * A y := by simp [Fin.prod_univ_succ,A]
    have e' (a : X) (y : Fin n → X) :
        (∏ i, g i ((Fin.cons (α := fun _ => X) a y) i)) = g 0 a * B y := by simp [Fin.prod_univ_succ,B]
    unfold l1DensityError
    rw [integral_cons μ (F := fun x =>
      ((∏ i, f i (x i)) - (∏ i, g i (x i))) + ((∏ i, g i (x i)) - (∏ i, f i (x i))))
      ((hF.sub hG).add (hG.sub hF)), Fin.sum_univ_succ]
    simp_rw [e,e']
    calc
      _ ≤ ∫⁻ y, ∫⁻ a, d a * A y + g 0 a * D y ∂μ ∂cubeMeasure μ n :=
        lintegral_mono (fun y => lintegral_mono (fun a => absDiff_mul _ _ _ _))
      _ = ∫⁻ y, (∫⁻ a, d a ∂μ) * A y + D y ∂cubeMeasure μ n := by
        apply lintegral_congr
        intro y
        rw [lintegral_add_left (f := fun a => d a * A y) (hd.mul_const _),
          lintegral_mul_const _ hd,lintegral_mul_const _ (hg 0),hgm,one_mul]
      _ = (∫⁻ a, d a ∂μ) + ∫⁻ y, D y ∂cubeMeasure μ n := by
        rw [lintegral_add_left (f := fun y => (∫⁻ a, d a ∂μ) * A y) (measurable_const.mul hA),
          lintegral_const_mul _ hA, hmA,mul_one]
      _ ≤ _ := add_le_add (le_refl _) (ih _ _ (fun i => hf i.succ) (fun i => hg i.succ)
        (fun i => hfm i.succ) (fun i => hgm i.succ))

/-- Triangle inequality for these extended `L¹` approximation bounds. -/
theorem l1DensityError_triangle {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F G H : X → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) (_hH : Measurable H) :
    l1DensityError μ F H ≤ l1DensityError μ F G + l1DensityError μ G H := by
  have directed (a b c : ℝ≥0∞) : a-c ≤ (a-b)+(b-c) := by
    apply tsub_le_iff_left.mpr
    calc
      a ≤ b+(a-b) := le_add_tsub
      _ ≤ (c+(b-c))+(a-b) := add_le_add_left le_add_tsub _
      _ = _ := by ac_rfl
  unfold l1DensityError
  rw [← lintegral_add_left (f := fun x => (F x-G x)+(G x-F x)) ((hF.sub hG).add (hG.sub hF))]
  apply lintegral_mono
  intro x
  calc
    _ ≤ _ := add_le_add (directed (F x) (G x) (H x)) (directed (H x) (G x) (F x))
    _ = _ := by ac_rfl

end LpGowers
