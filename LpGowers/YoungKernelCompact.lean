module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Compactness of weighted convolution

For finite target exponent, an Lᵠ family of rows of a bilinear pairing
defines a compact operator into Lᵠ. Approximation of its rows by finite
simple functions gives convergence in operator norm. Applying this fact
to translates of an Lᵖ' kernel proves compactness after an Lᵠ multiplier.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory MeasureTheory.Measure ContinuousLinearMap Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X} {q : ℝ≥0∞}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fact (1 ≤ q)]

/-- Pairing against an Lᵠ family of rows. -/
def rowPairing (B : E →L[ℝ] F →L[ℝ] ℝ) :
    Lp E q μ →L[ℝ] F →L[ℝ] Lp ℝ q μ := (B.flip.compLpL₂ q μ).flip

theorem rowPairing_apply_ae (B : E →L[ℝ] F →L[ℝ] ℝ) (K : Lp E q μ) (v : F) :
    rowPairing B K v =ᵐ[μ] fun x => B (K x) v :=
  (B.flip v).coeFn_compLp K

theorem isCompactOperator_rowPairing (hq : q ≠ ∞) (B : E →L[ℝ] F →L[ℝ] ℝ)
    (K : Lp E q μ) : IsCompactOperator (rowPairing B K) := by
  refine Lp.induction hq (fun K => IsCompactOperator (rowPairing B K)) ?_ ?_ ?_ K
  · intro c s hs hμs
    let I := indicatorConstLp q hs hμs.ne (1 : ℝ)
    rw [Lp.simpleFunc.coe_indicatorConst]
    have he : rowPairing B (indicatorConstLp q hs hμs.ne c) =
        (toSpanSingleton ℝ I).comp (B c) := by
      ext v : 1
      apply Lp.ext
      have hc := @indicatorConstLp_coeFn X E _ q μ _ s hs hμs.ne c
      have hI := @indicatorConstLp_coeFn X ℝ _ q μ _ s hs hμs.ne (1 : ℝ)
      filter_upwards [rowPairing_apply_ae B (indicatorConstLp q hs hμs.ne c) v,
        hc, hI, Lp.coeFn_smul (B c v) I] with x hx hcx hIx hS
      change _ = ((B c v) • I : Lp ℝ q μ) x
      rw [hx, hcx, hS]
      change _ = B c v • (indicatorConstLp q hs hμs.ne (1 : ℝ)) x
      rw [hIx]
      by_cases hm : x ∈ s <;> simp [hm]
    rw [he]
    exact (isCompactOperator_of_locallyCompactSpace_dom (B c)).clm_comp (toSpanSingleton ℝ I)
  · intro f g hf hg hd h₁ h₂
    rw [map_add]
    exact h₁.add h₂
  · exact isClosed_setOfPred_isCompactOperator.preimage (rowPairing B).continuous

section Convolution
variable {n : ℕ}
local notation "V" => Fin n → ℝ
local notation "m" => (volume : Measure V)
variable {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [p'.HolderConjugate p]


omit [Fact (1 ≤ q)] in
private theorem weighted_rows_memLp (κ : V × V → V) (hκ : Continuous κ)
    (hm : ∀ x : V, MeasurePreserving (fun y : V => κ (x,y)) m m) (hp' : p' ≠ ∞) (g : Lp ℝ p' m)
    {h : V → ℝ} (hh : MemLp h q m) :
    MemLp (fun x : V => h x • (Lp.compMeasurePreserving (fun y : V => κ (x,y)) (hm x) g : Lp ℝ p' m)) q m := by
  let ρ : C(V × V, V) := ⟨κ, hκ⟩
  have hc : Continuous fun x : V => Lp.compMeasurePreserving _ (hm x) g :=
    (continuous_const (y := g)).compMeasurePreservingLp ρ.curry.continuous hm hp'
  apply (hh.norm.const_mul ‖g‖).mono' (hh.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  exact ae_of_all _ fun x => by simp [norm_smul, mul_comm]

/-- Compactness of a continuous linear operator given by an Lᵖ' kernel with
continuously moving measure-preserving rows and an Lᵠ multiplier. Taking
κ(x,y) to be x-y, y-x or x+y gives all the derivative kernels. -/
theorem isCompactOperator_of_weighted_kernel (κ : V × V → V) (hκ : Continuous κ)
    (hm : ∀ x : V, MeasurePreserving (fun y : V => κ (x,y)) m m) (hp' : p' ≠ ∞) (hq : q ≠ ∞)
    {g h : V → ℝ} (hg : MemLp g p' m) (hh : MemLp h q m)
    (L : Lp ℝ p m →L[ℝ] Lp ℝ q m)
    (hL : ∀ f, L f =ᵐ[m] fun x => h x * ∫ y, g (κ (x,y)) * f y) : IsCompactOperator L := by
  let B := (lsmul ℝ ℝ (E := ℝ)).lpPairing m p' p
  let G := hg.toLp g
  have hK := weighted_rows_memLp κ hκ hm hp' G hh
  have he : L = rowPairing B (hK.toLp _) := by
    ext f : 1
    apply Lp.ext
    filter_upwards [rowPairing_apply_ae B (hK.toLp _) f, hK.coeFn_toLp, hL f] with x hout hrow hformula
    rw [hformula, hout, hrow]
    rw [B.map_smul, smul_apply, smul_eq_mul]
    congr 1
    rw [show B (Lp.compMeasurePreserving _ (hm x) G) f =
      ∫ y, (Lp.compMeasurePreserving _ (hm x) G) y * f y from
      (lsmul ℝ ℝ (E := ℝ)).lpPairing_eq_integral _ _]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving G (hm x),
      (hm x).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp] with y hy hgy
    exact congrArg (· * f y) (hy.trans hgy).symm
  rw [he]
  exact isCompactOperator_rowPairing hq _ _

/-- Compactness of convolution followed by an Lᵠ multiplier. -/
theorem isCompactOperator_of_weighted_convolution (hp' : p' ≠ ∞) (hq : q ≠ ∞)
    {g h : V → ℝ} (hg : MemLp g p' m) (hh : MemLp h q m)
    (L : Lp ℝ p m →L[ℝ] Lp ℝ q m)
    (hL : ∀ f, L f =ᵐ[m] fun x => h x * ∫ y, g (x-y) * f y) : IsCompactOperator L :=
  isCompactOperator_of_weighted_kernel _ (continuous_fst.sub continuous_snd)
    (measurePreserving_sub_left m) hp' hq hg hh L hL

/-- The kernel in the real autocorrelation, with argument x+y. -/
theorem isCompactOperator_of_weighted_correlation (hp' : p' ≠ ∞) (hq : q ≠ ∞)
    {g h : V → ℝ} (hg : MemLp g p' m) (hh : MemLp h q m)
    (L : Lp ℝ p m →L[ℝ] Lp ℝ q m)
    (hL : ∀ f, L f =ᵐ[m] fun x => h x * ∫ y, g (x+y) * f y) : IsCompactOperator L :=
  isCompactOperator_of_weighted_kernel _ (continuous_fst.add continuous_snd)
    (measurePreserving_add_left m) hp' hq hg hh L hL

/-- The kernel obtained by changing variables in the other autocorrelation
slot, with argument y-x. -/
theorem isCompactOperator_of_weighted_reversed_kernel (hp' : p' ≠ ∞) (hq : q ≠ ∞)
    {g h : V → ℝ} (hg : MemLp g p' m) (hh : MemLp h q m)
    (L : Lp ℝ p m →L[ℝ] Lp ℝ q m)
    (hL : ∀ f, L f =ᵐ[m] fun x => h x * ∫ y, g (y-x) * f y) : IsCompactOperator L :=
  isCompactOperator_of_weighted_kernel _ (continuous_snd.sub continuous_fst)
    (measurePreserving_sub_right m) hp' hq hg hh L hL

end Convolution
end LpGowers
