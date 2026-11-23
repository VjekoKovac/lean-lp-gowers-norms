module

public import LpGowers.DiscreteFunctional
public import LpGowers.ProductIntegral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Shared-increment configurations on a product lattice

The finite family of base points and the family of increments form one
configuration. Its projections onto the two factors of a lattice are
independent configurations. This is the Fubini step in Proposition 8.1. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers.Discrete

/-- An increment tuple followed by an ordered base-point tuple. -/
abbrev CubeConfigurations (G : Type*) (d p : ℕ) := (Fin d → G) × (Fin p → G)

/-- Vertex used by base point `j` and increment subset `s`. -/
def configurationVertex {G : Type*} [AddCommMonoid G] {d p : ℕ}
    (z : CubeConfigurations G d p) (j : Fin p) (s : Finset (Fin d)) : G :=
  z.2 j + ∑ i ∈ s, z.1 i

/-- The multilinear sum on the full countable group with counting measure. -/
def configurationSum {G : Type*} [AddCommMonoid G] (d p : ℕ)
    (F : Fin p → Finset (Fin d) → G → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' z : CubeConfigurations G d p, ∏ j, ∏ s, F j s (configurationVertex z j s)

/-- Tonelli separates the base points after fixing the common increments. -/
theorem tsum_configurations {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G] (d p : ℕ)
    (F : Fin p → Finset (Fin d) → G → ℝ≥0∞) :
    configurationSum d p F = ∑' h : Fin d → G, ∏ j, ∑' x, ∏ s, F j s (x+∑ i ∈ s,h i) := by
  rw [configurationSum,tsum_prod']
  apply tsum_congr
  intro h
  let T := fun (j : Fin p) (x : G) => ∏ s, F j s (x+∑ i ∈ s,h i)
  have ht (j) : Measurable (T j) := measurable_of_countable _
  have H := lintegral_pi_separated (Measure.count : Measure G) p T ht
  simpa only [cubeMeasure_count,lintegral_count,T,configurationVertex] using H

/-- Join a one-coordinate head and a remaining lattice tail. -/
def joinLattice (m : ℕ) : Lattice 1 × Lattice m ≃+ Lattice (m+1) where
  toFun z := Fin.cons (z.1 0) z.2
  invFun x := (fun _ => x 0,Fin.tail x)
  left_inv z := by
    apply Prod.ext
    · funext i
      have h : i=0 := Fin.eq_zero i
      simp [h]
    · simp
  right_inv x := Fin.cons_self_tail x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Splitting every base point and every increment gives an equivalence of
configuration spaces. -/
def joinConfigurations {H K G : Type*} [AddCommGroup H] [AddCommGroup K] [AddCommGroup G]
    (e : H × K ≃+ G) (d p : ℕ) :
    CubeConfigurations H d p × CubeConfigurations K d p ≃ CubeConfigurations G d p where
  toFun z := (fun i => e (z.1.1 i,z.2.1 i),fun j => e (z.1.2 j,z.2.2 j))
  invFun w := ((fun i => (e.symm (w.1 i)).1,fun j => (e.symm (w.2 j)).1),
    (fun i => (e.symm (w.1 i)).2,fun j => (e.symm (w.2 j)).2))
  left_inv z := by simp
  right_inv z := by simp

theorem configurationVertex_join {H K G : Type*} [AddCommGroup H] [AddCommGroup K] [AddCommGroup G]
    (e : H × K ≃+ G) {d p : ℕ} (u : CubeConfigurations H d p) (v : CubeConfigurations K d p)
    (j : Fin p) (s : Finset (Fin d)) :
    configurationVertex (joinConfigurations e d p (u,v)) j s =
      e (configurationVertex u j s, configurationVertex v j s) := by
  dsimp only [configurationVertex,joinConfigurations,Equiv.coe_fn_mk]
  rw [← map_sum,← map_add]
  congr 1
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

/-- Fubini splits a homogeneous configuration sum into a multilinear sum
of slices on the second factor, with slice indices supplied by the first. -/
theorem configurationSum_split {H K G : Type*} [AddCommGroup H] [AddCommGroup K] [AddCommGroup G]
    (e : H × K ≃+ G) (d p : ℕ) (f : G → ℝ≥0∞) :
    configurationSum d p (fun _ _ => f) =
    ∑' u : CubeConfigurations H d p, configurationSum d p
      (fun j s x => f (e (configurationVertex u j s,x))) := by
  unfold configurationSum
  rw [← (joinConfigurations e d p).tsum_eq
      (fun z : CubeConfigurations G d p => ∏ j, ∏ s, f (configurationVertex z j s)),tsum_prod']
  simp only [configurationVertex_join]

/-- A lattice point lies in its side-length-`n` box exactly when both factors do. -/
theorem joinLattice_mem_box (m n : ℕ) (b : Lattice 1) (x : Lattice m) :
    joinLattice m (b,x) ∈ box (m+1) n ↔ b ∈ box 1 n ∧ x ∈ box m n := by
  simp only [box,Fintype.mem_piFinset]
  constructor
  · intro h
    exact ⟨fun i => Fin.eq_zero i ▸ h 0,fun j => h j.succ⟩
  · rintro ⟨hb,hx⟩
    intro i
    exact Fin.cases (hb 0) (fun j => hx j) i

end LpGowers.Discrete
