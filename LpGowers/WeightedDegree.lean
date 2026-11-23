module

public import LpGowers.SymmetricLowering
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Interpolation between lower-order exponents

For positive weights the coordinatewise exponent equations identify a single
harmonic mean. Hölder interpolation then recovers the weighted lower product
from the symmetric degree-lowering inequality. -/

public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

/-- Finite positive-exponent interpolation, including infinite norms. -/
theorem lp_interpolate_fin {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {v : X → ℝ≥0∞} (hv : Measurable v)
    {s : ℝ} (hs : 0 < s) (q θ : ι → ℝ) (hq : ∀ i, 0 < q i) (hθ : ∀ i, 0 ≤ θ i)
    (hθsum : (∑ i, θ i) = 1) (hsum : (∑ i, θ i / q i) = 1 / s) :
    lp μ s v ≤ ∏ i, (lp μ (q i) v) ^ (θ i) := by
  let β := fun i => s * (θ i / q i)
  have hβ (i) : 0 ≤ β i := mul_nonneg hs.le (div_nonneg (hθ i) (hq i).le)
  have hβsum : (∑ i, β i) = 1 := by dsimp [β]; rw [← Finset.mul_sum, hsum]; field_simp
  have hqi (i) : q i * β i = s * θ i := by dsimp [β]; field_simp [(hq i).ne']
  have point (x : X) : (∏ i, (v x ^ (q i)) ^ (β i)) = v x ^ s := by
    simp only [← ENNReal.rpow_mul, hqi]
    rw [prod_const_rpow_of_nonneg _ _ _ (fun i => mul_nonneg hs.le (hθ i)),
      ← Finset.mul_sum, hθsum, mul_one]
  have H := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i x => v x ^ q i) (p := β)
    (fun i _ => (hv.pow_const (q i)).aemeasurable) hβsum (fun i _ => hβ i)
  simp_rw [point] at H
  apply (ENNReal.rpow_le_rpow H (by positivity : 0 ≤ 1/s)).trans_eq
  rw [← ENNReal.prod_rpow_of_nonneg (by positivity : 0 ≤ 1/s)]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [lp]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  congr 1
  dsimp [β]
  field_simp

/-- Interpolation with the cube norm's outer power included. -/
theorem gowers_interpolate_fin {G ι : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [Fintype ι] (μ : Measure G) [SFinite μ] [μ.IsAddLeftInvariant]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) {s : ℝ} (hs : 0 < s)
    (q θ : ι → ℝ) (hq : ∀ i, 0 < q i) (hθ : ∀ i, 0 ≤ θ i)
    (hθsum : (∑ i, θ i) = 1) (hsum : (∑ i, θ i / q i) = 1 / s) :
    gowers μ k s f ≤ ∏ i, (gowers μ k (q i) f) ^ (θ i) := by
  have H := lp_interpolate_fin (cubeMeasure μ k) (measurable_autocorrelation_of_aemeasurable μ k hf)
    hs q θ hq hθ hθsum hsum
  apply (ENNReal.rpow_le_rpow H (by positivity : 0 ≤ 1/(2:ℝ)^k)).trans_eq
  rw [← ENNReal.prod_rpow_of_nonneg (by positivity : 0 ≤ 1/(2:ℝ)^k)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [gowers, ← ENNReal.rpow_mul, mul_comm (θ i)]

/-- Harmonic-mean parameters for the positive-weight regime of (1.9).
`Q` is the lower exponent in the symmetric instance of (3.3). -/
theorem harmonicLowerExponent {k : ℕ} (hk : 1 ≤ k) {p : ℝ} {q θ : Fin (k+1) → ℝ}
    (h : DegreeParameters k p q θ) (hp : DegreeForward p θ) :
    ∃ Q : ℝ, 0 < Q ∧ Q ≤ 2 ∧ (k+1 : ℝ) * Q / (2*k + Q) = p ∧
      (∑ i, θ i / q i) = 1 / Q := by
  obtain ⟨hq, hsum, hrel⟩ := h
  obtain ⟨hp, hp1, _⟩ := hp
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hden : 0 < (k : ℝ)+1-p := by linarith
  let Q := 2*k*p / ((k:ℝ)+1-p)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have he (i) : θ i / q i = (θ i - (1-1/p)/k) * (1/2) := by
    have hi := hrel i
    norm_num only [Nat.cast_ofNat] at hi
    field_simp [(hq i).ne', hp.ne', hk'.ne'] at hi ⊢
    nlinarith
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hk'.le (sub_nonneg.mpr hp1)]
  · have hn : 0 < 2*(k:ℝ) + Q := by positivity
    apply (div_eq_iff hn.ne').2
    dsimp [Q]
    field_simp [hden.ne']
    ring
  · simp_rw [he]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    dsimp [Q]
    field_simp [hp.ne', hk'.ne', hden.ne']
    ring

/-- The full forward inequality in Theorem 1.4(a), including its closed endpoint. -/
theorem degree_forward {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {k : ℕ} (hk : 1 ≤ k) {p : ℝ} {q θ : Fin (k+1) → ℝ}
    (h : DegreeParameters k p q θ) (hp : DegreeForward p θ) {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) : gowers μ (k+1) p f ≤ lowerProduct μ k q θ f := by
  obtain ⟨Q,hQ,_,hscale,hm⟩ := harmonicLowerExponent hk h hp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hj : 0 < (j:ℝ) + 1 := by positivity
  have hj' : 0 < (j:ℝ) + 2 := by positivity
  push_cast at hscale
  have hden : 0 < 2 * ((j:ℝ) + 1) + Q := by positivity
  have he := (div_eq_iff hden.ne').mp hscale
  have hrel : Q * (1 / ((j:ℝ) + 1)) * (1-p) + (Q-2) * (p / ((j:ℝ) + 2)) = 0 := by
    field_simp [hj.ne', hj'.ne']
    nlinarith only [he]
  exact (degree_symmetric μ j hp.1 hp.2.1 hQ hrel hf).trans
    (gowers_interpolate_fin μ hf (j+1) hQ q θ h.1 (fun i => (hp.2.2 i).le) h.2.1 hm)

end LpGowers
