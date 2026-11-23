module

public import LpGowers.Euclidean
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-! # A finite-dimensional space of affine quadratic logarithms

The coefficients are a scalar, a linear form, and a symmetric matrix. A
positive measure uniqueness set for multivariable polynomials is therefore
also a uniqueness set for these fields. Finite-dimensional topology then
upgrades pointwise convergence on the uniqueness set to global convergence.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix
namespace LpGowers

/-- Symmetry of the matrix is imposed before taking the image as functions. -/
def symmetricCoefficient (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {P | ∀ i j, P i j=P j i}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hQ hP i j => by simp [Matrix.add_apply,hQ i j,hP i j]
  smul_mem' := fun c P hP i j => by simp [Matrix.smul_apply,hP i j]

abbrev QuadCoeff (n : ℕ) := ℝ × Rn n × symmetricCoefficient n

def coefficientField (n : ℕ) : QuadCoeff n →ₗ[ℝ] (Rn n → ℝ) where
  toFun C x := C.1 + ∑ i, C.2.1 i * x i - ∑ i, ∑ j, (C.2.2.1 i j)*(x i*x j)
  map_add' := by
    intro U V
    funext x
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Submodule.coe_add,Matrix.add_apply,add_mul,
      Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c V
    funext x
    change c*V.1 + (∑ i, (c*V.2.1 i)*x i) - (∑ i, ∑ j, (c*V.2.2.1 i j)*(x i*x j)) =
      c*(V.1 + (∑ i, V.2.1 i*x i) - (∑ i, ∑ j,V.2.2.1 i j*(x i*x j)))
    simp only [mul_sub,mul_add,Finset.mul_sum,mul_assoc]

/-- The space of affine quadratic polynomials viewed as actual real-valued
functions, with the topology of pointwise convergence. -/
def quadraticLogSpace (n : ℕ) := (coefficientField n).range

instance quadraticLogSpace_finite (n : ℕ) : FiniteDimensional ℝ (quadraticLogSpace n) := by
  unfold quadraticLogSpace
  infer_instance

private theorem coefficientField_eval (n : ℕ) (C : QuadCoeff n) (x : Rn n) :
    coefficientField n C x = C.1 + x ⬝ᵥ C.2.1 - gaussianQuad C.2.2.1 x := by
  simp only [coefficientField,LinearMap.coe_mk,AddHom.coe_mk, dotProduct,gaussianQuad]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem mem_quadraticLogSpace {n : ℕ} {g : Rn n → ℝ} :
    g ∈ quadraticLogSpace n ↔ ∃ (a : ℝ) (b : Rn n) (P : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j,P i j=P j i) ∧ ∀ x,g x=a+x ⬝ᵥ b-gaussianQuad P x := by
  constructor
  · rintro ⟨C,rfl⟩
    exact ⟨C.1,C.2.1,C.2.2.1,C.2.2.2,coefficientField_eval n C⟩
  · rintro ⟨a,b,P,hP,hg⟩
    let C : QuadCoeff n := (a,b,⟨P,hP⟩)
    exact ⟨C,funext fun x => (coefficientField_eval n C x).trans (hg x).symm⟩

theorem exists_polynomial_of_quadraticLogSpace {n : ℕ} {g : Rn n → ℝ} (hg : g ∈ quadraticLogSpace n) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ x,MvPolynomial.eval x P = g x := by
  obtain ⟨a,b,M,_,H⟩ := mem_quadraticLogSpace.mp hg
  refine ⟨MvPolynomial.C a + ∑ i, MvPolynomial.X i * MvPolynomial.C (b i) -
    ∑ i, ∑ j,MvPolynomial.X i * MvPolynomial.C (M i j) * MvPolynomial.X j,?_⟩
  intro x
  simp [H,dotProduct,gaussianQuad]

/-- Pointwise limits on a uniqueness set give pointwise convergence on
every point. No bound on the sequence of coefficients is assumed. -/
theorem finite_dimensional_restriction_limit {X : Type*} (V : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ V] (S : Set X) (hunique : ∀ v : V, (∀ x ∈ S, (v : X→ℝ) x=0) → v=0)
    (u : ℕ → V) (g : S → ℝ)
    (hconv : ∀ x:S,Tendsto (fun k => (u k : X→ℝ) x) atTop (𝓝 (g x))) :
    ∃ v : V, ∀ x : X,Tendsto (fun k => (u k : X→ℝ) x) atTop (𝓝 ((v : X→ℝ) x)) := by
  let L : V →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun v x => (v : X → ℝ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot.mp ?_)
    rw [Submodule.eq_bot_iff]
    intro y hy
    exact hunique y (fun x hx => congrFun (show L y=0 from hy) ⟨x,hx⟩)
  let e := LinearEquiv.ofInjective L hinj
  have h := tendsto_pi_nhds.mpr hconv
  change Tendsto (fun k => L (u k)) atTop (𝓝 g) at h
  have hgr : g ∈ L.range := L.range.isClosed_of_finiteDimensional.mem_of_tendsto h
    (Eventually.of_forall fun k => ⟨u k,rfl⟩)
  let v := e.symm ⟨g,hgr⟩
  have hr : Tendsto (fun k => e (u k)) atTop (𝓝 ⟨g,hgr⟩) := tendsto_subtype_rng.mpr h
  have hu : Tendsto u atTop (𝓝 v) := by
    have hh := e.symm.toLinearMap.continuous_of_finiteDimensional.continuousAt.tendsto.comp hr
    change Tendsto (fun k => e.symm (e (u k))) atTop (𝓝 v) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  refine ⟨v,fun x => ?_⟩
  exact ((continuous_apply x).comp continuous_subtype_val).continuousAt.tendsto.comp hu

end LpGowers
