module

public import LpGowers.YoungLocalCompact
public import LpGowers.YoungUpdateMap
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Tactic

/-! Compactness of the strict derivative of the normalized diagonal Young
update. The two compact operators are the two Gaussian convolutions at the
outer bilinear step, followed by the derivative of the final pointwise power. -/
@[expose] public section
namespace LpGowers
open Filter
open scoped Topology
variable {E Y V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A bounded inner derivative and the two compact weighted convolutions of
the outer stage give a compact derivative for the entire Euler update. -/
theorem youngUpdate_compact_derivative (c : ℝ) (A : E →L[ℝ] E →L[ℝ] Y)
    (B : V →L[ℝ] E →L[ℝ] W) (P : Y → V) (Q : W → E) (G : E)
    {P' : Y →L[ℝ] V} {Q' : W →L[ℝ] E}
    (hp : HasStrictFDerivAt P P' (A G G))
    (hq : HasStrictFDerivAt Q Q' (B (P (A G G)) G))
    (h₁ : IsCompactOperator (Q'.comp (B (P (A G G)))))
    (h₂ : IsCompactOperator (Q'.comp (B.flip G))) :
    ∃ L : E →L[ℝ] E,
      HasStrictFDerivAt (youngUpdateMap c A B P Q) L G ∧ IsCompactOperator L := by
  let C := A G + A.flip G
  have ha : HasStrictFDerivAt (fun x => A x x) C G := by
    convert A.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id G) (hasStrictFDerivAt_id G) using 1
    all_goals rfl
  let D := P'.comp C
  have hd : HasStrictFDerivAt (fun x => P (A x x)) D G := hp.comp (f := fun x => A x x) G ha
  let J := B (P (A G G)) + (B.flip G).comp D
  have hj : HasStrictFDerivAt (fun x => B (P (A x x)) x) J G := by
    convert B.hasStrictFDerivAt_of_bilinear hd (hasStrictFDerivAt_id G) using 1
    all_goals rfl
  refine ⟨c • Q'.comp J,(hq.comp (f := fun x => B (P (A x x)) x) G hj).const_smul c,?_⟩
  have hsum := h₁.add (h₂.comp_clm D)
  convert hsum.smul c using 1
  ext x
  simp [J,Function.comp_apply]

/-- Local strong precompactness for the Young update after verifying the two
weighted-convolution compactness statements and the two power derivatives. -/
theorem youngUpdate_local_precompact [CompleteSpace E] (c : ℝ)
    (A : E →L[ℝ] E →L[ℝ] Y) (B : V →L[ℝ] E →L[ℝ] W)
    (P : Y → V) (Q : W → E) (G : E)
    {P' : Y →L[ℝ] V} {Q' : W →L[ℝ] E}
    (hp : HasStrictFDerivAt P P' (A G G))
    (hq : HasStrictFDerivAt Q Q' (B (P (A G G)) G))
    (h₁ : IsCompactOperator (Q'.comp (B (P (A G G)))))
    (h₂ : IsCompactOperator (Q'.comp (B.flip G))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℕ → E, (∀ k, dist (u k) G < ε) →
      Tendsto (fun k => u k - youngUpdateMap c A B P Q (u k)) atTop (𝓝 0) →
      ∃ g : E, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (u ∘ σ) atTop (𝓝 g) := by
  obtain ⟨L,hL,hc⟩ := youngUpdate_compact_derivative c A B P Q G hp hq h₁ h₂
  exact exists_local_approx_fixed_precompact hL hc

end LpGowers
