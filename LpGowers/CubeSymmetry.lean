module

public import LpGowers.DegreeProofs
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! # Symmetry in the cube increments -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers

/-- Permuting the increments permutes the cube vertices, including all
multiplicities when some increments agree. -/
theorem cubeProduct_perm {G : Type*} [AddCommMonoid G] (n : ℕ) (f : G → ℝ≥0)
    (σ : Equiv.Perm (Fin n)) (h : Fin n → G) (x : G) :
    cubeProduct n f (h ∘ σ) x = cubeProduct n f h x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero =>
      have H : h ∘ σ = h := funext fun i => congrArg h ((Fin.eq_zero (σ i)).trans (Fin.eq_zero i).symm)
      rw [H]
    | succ n =>
      obtain ⟨⟨i,π⟩,rfl⟩ := Equiv.Perm.decomposeFin'.symm.surjective σ
      let z := i.removeNth h
      have hz : i.insertNth (h i) z = h := Fin.insertNth_self_removeNth _ _
      rw [← hz, cubeProduct_insertNth, hz]
      change cubeProduct (n+1) f (z ∘ π) x * cubeProduct (n+1) f (z ∘ π) (x + h i) = _
      rw [ih π z, ih π z]

/-- Permutation symmetry is pointwise in the increments and requires no
measurability assumption on the input. -/
theorem autocorrelation_perm {G : Type*} [AddCommMonoid G] [MeasurableSpace G]
    (μ : Measure G) (n : ℕ) (f : G → ℝ≥0) (σ : Equiv.Perm (Fin n)) (h : Fin n → G) :
    autocorrelation μ n f (h ∘ σ) = autocorrelation μ n f h :=
  lintegral_congr fun x => cubeProduct_perm n f σ h x

/-- A permutation preserves the common finite product measure. -/
theorem cubeMeasure_perm {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → X => x ∘ σ) (cubeMeasure μ n) (cubeMeasure μ n) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) σ
  have he : MeasurePreserving e (cubeMeasure μ n) (cubeMeasure μ n) :=
    measurePreserving_piCongrLeft (fun _ => μ) σ
  have hm := MeasurePreserving.symm e he
  convert hm using 1
  funext x i
  exact (Equiv.piCongrLeft_symm_apply (fun _ : Fin n => X) σ x i).symm

end LpGowers
