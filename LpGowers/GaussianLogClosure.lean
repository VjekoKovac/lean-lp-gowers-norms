module

public import LpGowers.QuadraticLogSpace
public import LpGowers.PolynomialZeroSet

/-! # Removing the heat regularization in Gaussian rigidity

On the positive part of the limiting density, logarithms converge almost
everywhere. A nonzero quadratic cannot vanish on that positive-measure set.
Restriction of the finite-dimensional space of logarithms is thus injective,
giving convergence of the logarithms at every point. Exponentiating identifies
the original density up to almost-everywhere equality. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix
namespace LpGowers

/-- A nonzero almost-everywhere limit of positive exponentials of affine
quadratics has an almost-everywhere positive representative of the same form.
The quadratic matrices remain symmetric. -/
theorem ae_exp_quadratic_limit {n : ℕ} (G : ℕ → Rn n → ℝ) (f : Rn n → ℝ)
    (hnonneg : ∀ᵐ x ∂volume,0 ≤ f x) (hnonzero : ¬ f =ᵐ[volume] 0)
    (hG : ∀ k, ∃ (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j,P i j=P j i) ∧ ∀ x,G k x=Real.exp (a+x ⬝ᵥ b-gaussianQuad P x))
    (hconv : ∀ᵐ x ∂volume,Tendsto (fun k => G k x) atTop (𝓝 (f x))) :
    ∃ (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j,P i j=P j i) ∧ ∀ᵐ x ∂volume,f x=Real.exp (a+x ⬝ᵥ b-gaussianQuad P x) := by
  classical
  choose a b P hP hre using hG
  let V := quadraticLogSpace n
  let U (k : ℕ) : V := ⟨fun x => a k + x ⬝ᵥ b k - gaussianQuad (P k) x,
    mem_quadraticLogSpace.mpr ⟨a k,b k,P k,hP k,fun _ => rfl⟩⟩
  let S := {x : Rn n | 0 < f x ∧ Tendsto (fun k => G k x) atTop (𝓝 (f x))}
  have hS : volume S ≠ 0 := by
    intro hz
    apply hnonzero
    have hSae : ∀ᵐ x ∂volume,x ∉ S := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    filter_upwards [hnonneg,hconv,hSae] with x hx hc hs
    change f x=0
    exact le_antisymm (le_of_not_gt fun h => hs ⟨h,hc⟩) hx
  have hunique (v : V) (h : ∀x∈S,(v : Rn n → ℝ) x=0) : v=0 := by
    obtain ⟨p,hp⟩ := exists_polynomial_of_quadraticLogSpace v.2
    have hp0 : p=0 := by
      by_contra hp'
      have he := ae_mvPolynomial_eval_ne_zero n p hp'
      apply hS
      apply measure_mono_null (t:={x | ¬ MvPolynomial.eval x p ≠ 0}) ?_ (ae_iff.mp he)
      intro x hx
      exact fun hn => hn ((hp x).trans (h x hx))
    apply Subtype.ext
    funext x
    change (v : Rn n → ℝ) x=0
    simpa only [hp0,map_zero] using (hp x).symm
  have hlog (x:S) : Tendsto (fun k => (U k : Rn n → ℝ) x) atTop (𝓝 (Real.log (f x))) := by
    have h := (Real.continuousAt_log x.property.1.ne').tendsto.comp x.property.2
    simpa only [Function.comp_def,fun k => hre k x,Real.log_exp,U] using h
  obtain ⟨v,hv⟩ := finite_dimensional_restriction_limit V S hunique U _ hlog
  obtain ⟨c,w,M,hM,heq⟩ := mem_quadraticLogSpace.mp v.2
  refine ⟨c,w,M,hM,?_⟩
  filter_upwards [hconv] with x hx
  have h := Real.continuous_exp.continuousAt.tendsto.comp (hv x)
  have hseq : (fun k => G k x) = (fun k => Real.exp ((U k : Rn n → ℝ) x)) :=
    funext (fun k => hre k x)
  rw [hseq] at hx
  rw [← heq x]
  exact tendsto_nhds_unique hx h

end LpGowers
