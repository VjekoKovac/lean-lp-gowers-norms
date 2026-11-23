module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Stability of the weighted arithmetic–geometric mean

A scalar estimate used to control near equality of moments in §6 of
Kovač–Rogers. The proof applies Mathlib's weighted AM–GM inequality to
`√A * √B` and to the more heavily weighted endpoint.
-/

@[expose] public section

namespace LpGowers

private theorem sqrt_deficit_of_weight_le {a b A B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hs : a + b = 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    a * (Real.sqrt A - Real.sqrt B)^2 ≤ a*A + b*B - A^a * B^b := by
  have hx := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ 2*a by linarith)
    (sub_nonneg.mpr hab) (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)) hB
    (show 2*a + (b-a) = 1 by linarith)
  have he : (Real.sqrt A * Real.sqrt B) ^ (2*a) * B ^ (b-a) = A^a * B^b := by
    rw [Real.mul_rpow (Real.sqrt_nonneg A) (Real.sqrt_nonneg B),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA,
      ← Real.rpow_mul hB, show 1/(2:ℝ)*(2*a) = a by ring, mul_assoc,
      ← Real.rpow_add_of_nonneg hB ha (sub_nonneg.mpr hab), show a+(b-a)=b by ring]
  rw [he] at hx
  calc
    a * (Real.sqrt A - Real.sqrt B)^2 =
        a * Real.sqrt A ^ 2 + b * Real.sqrt B ^ 2 -
        (2*a * (Real.sqrt A * Real.sqrt B) + (b-a) * Real.sqrt B ^ 2) := by ring
    _ = a*A + b*B - (2*a * (Real.sqrt A * Real.sqrt B) + (b-a)*B) := by
        rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
    _ ≤ a*A + b*B - A^a * B^b := sub_le_sub_left hx _

/-- The weighted AM–GM deficit controls the squared distance between the square roots. -/
theorem sqrt_deficit_le {θ A B : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min θ (1-θ) * (Real.sqrt A - Real.sqrt B)^2 ≤
      θ*A + (1-θ)*B - A^θ * B^(1-θ) := by
  rcases le_total θ (1-θ) with h | h
  · rw [min_eq_left h]
    exact sqrt_deficit_of_weight_le hθ h (by ring) hA hB
  · rw [min_eq_right h, ← neg_sub (Real.sqrt B) (Real.sqrt A), neg_sq,
      add_comm (θ*A), mul_comm (A^θ)]
    exact sqrt_deficit_of_weight_le (sub_nonneg.mpr hθ') h (by ring) hB hA

open MeasureTheory

/-- Integrated stability for finite first moments. Both the square-root error
and the mixed moment are integrable under the stated endpoint assumptions. -/
theorem integral_sqrt_deficit_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) {A B : X → ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hA₀ : 0 ≤ᵐ[μ] A) (hB₀ : 0 ≤ᵐ[μ] B) :
    min θ (1-θ) * (∫ x, (Real.sqrt (A x) - Real.sqrt (B x))^2 ∂μ) ≤
      θ * (∫ x, A x ∂μ) + (1-θ) * (∫ x, B x ∂μ) - (∫ x, A x^θ * B x^(1-θ) ∂μ) := by
  have ht : 0 ≤ 1-θ := sub_nonneg.mpr hθ'
  have hsum := (hA.const_mul θ).add (hB.const_mul (1-θ))
  have hG : Integrable (fun x => A x^θ * B x^(1-θ)) μ := by
    apply hsum.mono' ((hA.aemeasurable.pow_const _).mul (hB.aemeasurable.pow_const _)).aestronglyMeasurable
    filter_upwards [hA₀, hB₀] with x ha hb
    change ‖A x ^ θ * B x ^ (1-θ)‖ ≤ θ * A x + (1-θ) * B x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))]
    exact Real.geom_mean_le_arith_mean2_weighted hθ ht ha hb (by ring)
  have hS : Integrable (fun x => (Real.sqrt (A x) - Real.sqrt (B x))^2) μ := by
    apply (hA.add hB).mono' ((hA.aemeasurable.sqrt.sub hB.aemeasurable.sqrt).pow_const 2).aestronglyMeasurable
    filter_upwards [hA₀, hB₀] with x ha hb
    change ‖(Real.sqrt (A x)-Real.sqrt (B x))^2‖ ≤ A x + B x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg (A x)) (Real.sqrt_nonneg (B x))]
  have hi := integral_mono_ae (hS.const_mul (min θ (1-θ))) (hsum.sub hG)
    (by filter_upwards [hA₀,hB₀] with x ha hb using sqrt_deficit_le hθ hθ' ha hb)
  simpa only [integral_sub' hsum hG, integral_add' (hA.const_mul θ) (hB.const_mul (1-θ)),
    integral_const_mul] using hi

/-- Quantitative first step of Lemma 6.2. If the endpoint moments are at most
`1+ε` and the intermediate moment is at least `1-ε`, the two square-root
endpoint densities have small squared L² distance. -/
theorem three_moment_sqrt_deficit {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ} (hF : 0 ≤ᵐ[μ] F) {a b c θ ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hb : a*θ + c*(1-θ) = b)
    (hA : Integrable (fun x => F x ^ a) μ) (hC : Integrable (fun x => F x ^ c) μ)
    (hMa : (∫ x, F x ^ a ∂μ) ≤ 1+ε) (hMc : (∫ x, F x ^ c ∂μ) ≤ 1+ε)
    (hMb : 1-ε ≤ ∫ x, F x ^ b ∂μ) :
    min θ (1-θ) * (∫ x, (Real.sqrt (F x ^ a) - Real.sqrt (F x ^ c))^2 ∂μ) ≤ 2*ε := by
  have hθ₂ := sub_nonneg.mpr hθ'
  have hI := integral_sqrt_deficit_le μ hθ hθ' hA hC
    (hF.mono fun x hx => Real.rpow_nonneg hx a) (hF.mono fun x hx => Real.rpow_nonneg hx c)
  have hm : (∫ x, (F x ^ a)^θ * (F x ^ c)^(1-θ) ∂μ) = ∫ x, F x ^ b ∂μ := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [← Real.rpow_mul hx, ← Real.rpow_mul hx,
      ← Real.rpow_add_of_nonneg hx (mul_nonneg ha hθ) (mul_nonneg hc hθ₂), hb]
  rw [hm] at hI
  apply hI.trans
  calc
    _ ≤ θ*(1+ε) + (1-θ)*(1+ε) - (1-ε) :=
      sub_le_sub (add_le_add (mul_le_mul_of_nonneg_left hMa hθ)
        (mul_le_mul_of_nonneg_left hMc hθ₂)) hMb
    _ = 2*ε := by ring

end LpGowers
