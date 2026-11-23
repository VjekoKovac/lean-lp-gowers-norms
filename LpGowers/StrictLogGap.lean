module

public import LpGowers.LogNormalization
public import LpGowers.LogBox
public import LpGowers.BoxSymmetry
public import LpGowers.SliceTolerance
public import LpGowers.BoxSubgroup

/-! Theorem 1.1 of Kovač and Rogers. The proof follows the two-dimensional
slice of §6. Permutation symmetry gives comparable box sides directly.
The contradiction uses the alternative small-difference argument described
at the end of the source proof. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LpGowers

theorem improved_log_convexity.{u} : ImprovedLogConvexity.{u} := by
  apply improvedLogConvexity_iff_normalized.mpr
  intro d hd
  obtain ⟨k,hk⟩ : ∃ k, d = k+2 := ⟨d-2, by omega⟩
  subst d
  obtain ⟨η,hη,hη',close⟩ := compact_open_of_boxError.{u}
  obtain ⟨τ,hτ,hτη,slice⟩ := good_slice_of_near_unit_sides.{u} k hη hη'
  obtain ⟨σ,hσ,allSides⟩ := symmetric_box_sides.{u} hτ
  let ρ := min τ σ
  have hρ : 0 < ρ := lt_min hτ hσ
  obtain ⟨ε,hε,hε',box⟩ := normalized_log_box.{u} k ρ hρ
  refine ⟨ε,hε,hε',?_⟩
  intro G _ _ _ _ _ _ _ _ μ _ hG f hf hlow hhigh
  rw [show k+2-1=k+1 by omega] at hlow
  by_contra! hlarge
  obtain ⟨A,hA,hm,herr⟩ := box G μ f hf hlow hhigh hlarge.le
  let ν := cubeMeasure μ (k+2)
  let F := autocorrelation μ (k+2) f
  let B := univ.pi A
  have herr' : boxError μ (k+2) f A ≤ ENNReal.ofReal ρ := herr
  have hl : l1DensityError ν F (B.indicator 1) ≤ ENNReal.ofReal σ := by
    apply le_trans _ (herr.trans (ENNReal.ofReal_le_ofReal (min_le_right ..)))
    exact lintegral_mono fun _ => le_self_add
  have side := allSides μ (k+1) F (measurable_autocorrelation_of_aemeasurable μ _ hf)
    (autocorrelation_perm μ _ f) A (fun i => (hA i).1) (hm.trans (min_le_right ..)) hl
  have bounds (i : Fin (k+2)) :
      ENNReal.ofReal (1-τ) ≤ μ (A i) ∧ μ (A i) ≤ ENNReal.ofReal (1+τ) := by
    have hs := abs_le.mp (side i).2.2
    have eq : ENNReal.ofReal (μ.real (A i)) = μ (A i) :=
      ENNReal.ofReal_toReal (hA i).2.2
    constructor
    · rw [← eq]; exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← eq]; exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨z,hz,hmz⟩ := slice μ hf hlow A (fun i => (hA i).1) (fun i => (bounds i).1)
    (herr'.trans (ENNReal.ofReal_le_ofReal (min_le_left ..)))
  have lo (i : Fin (k+2)) : ENNReal.ofReal (1-η) ≤ μ (A i) :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans (bounds i).1
  have hi (i : Fin (k+2)) : μ (A i) ≤ ENNReal.ofReal (1+η) :=
    (bounds i).2.trans (ENNReal.ofReal_le_ofReal (by linarith))
  exact hG (close G μ (sliceInput k f z) (sliceInput_aemeasurable μ hf k z)
    (A 0) (A 1) (hA 0).1 (hA 1).1 (lo _) (hi _) (lo _) (hi _) hmz hz)

end LpGowers
