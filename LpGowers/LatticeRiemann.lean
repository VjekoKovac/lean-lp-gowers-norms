module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic

/-! # Cubical Riemann sums over the whole integer lattice

Mathlib's unit-partition theorem sums over a subtype of the ambient real
vector space. Here the sum is written over integer tuples, as in the energy
expansion in Section 8. The support hypothesis inserts the integration box
without changing the discrete or continuous values. -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Bornology
open scoped Pointwise Topology
namespace LpGowers.Discrete

/-- A real grid point of mesh size `1/n`. -/
def gridPoint {ι : Type*} (n : ℕ) (z : ι → ℤ) (i : ι) : ℝ := (z i:ℝ)/n

private def gridBoxEquiv {ι : Type*} [Fintype ι] (n : ℕ) [NeZero n] (S : Set (ι → ℝ)) :
    {z : ι → ℤ // gridPoint n z ∈ S} ≃
      ↑(S ∩ (n:ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  classical
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let g := fun z : {z : ι → ℤ // gridPoint n z ∈ S} =>
    (⟨gridPoint n z.1,z.2,BoxIntegral.unitPartition.mem_smul_span_iff.mpr
       (fun i => ⟨z.1 i,by change (z.1 i:ℝ)=(n:ℝ)*((z.1 i:ℝ)/n); field_simp⟩)⟩ :
      ↑(S ∩ (n:ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))
  apply Equiv.ofBijective g
  constructor
  · intro a b e
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Subtype.val e) i
    change (a.1 i:ℝ)/n = (b.1 i:ℝ)/n at hi
    exact_mod_cast (div_left_inj₀ hn).mp hi
  · intro y
    obtain ⟨z,hz⟩ := Classical.axiomOfChoice (BoxIntegral.unitPartition.mem_smul_span_iff.mp y.2.2)
    have he : gridPoint n z=y.1 := by
      funext i
      apply (div_eq_iff hn).mpr
      simpa [mul_comm] using hz i
    exact ⟨⟨z,he ▸ y.2.1⟩,Subtype.ext he⟩

/-- Full-lattice Riemann sums for continuous compactly supported functions
in any bounded Jordan-measurable set. -/
theorem tendsto_lattice_sum {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ)
    (hF : Continuous F) (hb : IsBounded S) (hm : MeasurableSet S) (hfr : volume (frontier S)=0)
    (hs : ∀ x,x∉S → F x=0) :
    Tendsto (fun n : ℕ => (∑' z : ι → ℤ, F (gridPoint n z)) / (n:ℝ)^(Fintype.card ι))
      atTop (𝓝 (∫ x, F x)) := by
  classical
  have H := tendsto_tsum_div_pow_atTop_integral S F hF hb hm hfr
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  congr 1
  let T : Set (ι → ℤ) := {z | gridPoint n z ∈ S}
  let L := S ∩ (n:ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  calc
    (∑' x : L, F x) = ∑' z : T, F (gridPoint n (z : ι → ℤ)) :=
      ((gridBoxEquiv n S).tsum_eq (fun x : L => F x)).symm
    _ = _ := by
      rw [tsum_subtype T (fun z => F (gridPoint n z))]
      apply tsum_congr
      intro z
      by_cases hz : z ∈ T
      · simp [hz]
      · simp [hz,hs _ hz]

end LpGowers.Discrete
