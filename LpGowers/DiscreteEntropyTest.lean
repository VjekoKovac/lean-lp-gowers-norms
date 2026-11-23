module

public import LpGowers.DiscreteSignedCube
import Mathlib.Tactic

/-! # The binomial test for the large-degree lower bound

Choose the active directions and then independently choose a positive or a
negative unit increment in each. Every such configuration contributes its
binomial vertex product to the one-dimensional weighted energy. -/

@[expose] public section
noncomputable section
open scoped NNReal BigOperators Pointwise
namespace LpGowers.Discrete

private abbrev Pattern (d l : ℕ) :=
  (S : ↥(Finset.univ.powersetCard l : Finset (Finset (Fin d)))) × (S.1 → Bool)

private def patternCode {d l : ℕ} (p : Pattern d l) (i : Fin d) : Option Bool :=
  if h : i ∈ p.1.1 then some (p.2 ⟨i,h⟩) else none

private theorem patternCode_injective (d l : ℕ) :
    Function.Injective (patternCode (d := d) (l := l)) := by
  classical
  rintro ⟨⟨S,hS⟩,a⟩ ⟨⟨T,hT⟩,b⟩ e
  have hST : S = T := by
    ext i
    have E := congrFun e i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all [patternCode]
  subst T
  have hab : a=b := by
    funext i
    have E := congrFun e i.val
    simpa [patternCode,i.property] using E
  subst b
  rfl

private def patternSteps (d l : ℕ) : Pattern d l ↪ (Fin d → Lattice 1) where
  toFun p i _ := unitShift (patternCode p i)
  inj' := by
    intro p q e
    apply patternCode_injective d l
    funext i
    have H := congrFun (congrFun e i) 0
    change unitShift (patternCode p i) = unitShift (patternCode q i) at H
    cases hp : patternCode p i with
    | none => cases hq : patternCode q i with
              | none => rfl
              | some c => cases c <;> simp [hp,hq,unitShift] at H
    | some b => cases hq : patternCode q i with
                | none => cases b <;> simp [hp,hq,unitShift] at H
                | some c => cases b <;> cases c <;> simp_all [unitShift]

private theorem patternCount (d l : ℕ) : Fintype.card (Pattern d l) = d.choose l * 2^l := by
  classical
  rw [Fintype.card_sigma]
  have hcard (S : ↥(Finset.univ.powersetCard l : Finset (Finset (Fin d)))) : S.1.card = l :=
    (Finset.mem_powersetCard.mp S.2).2
  simp [hcard]

private theorem patternSupport {d l : ℕ} (p : Pattern d l) : signedSupport (patternCode p) = l := by
  unfold signedSupport
  have h (i : Fin d) : (if (patternCode p i).isSome then 1 else 0) =
      (if i ∈ p.1.1 then 1 else 0 : ℕ) := by by_cases hi : i ∈ p.1.1 <;> simp [patternCode,hi]
  simp only [h, Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter,Nat.cast_id]
  exact (Finset.mem_powersetCard.mp p.1.2).2

private theorem negativeCount_le_support {d : ℕ} (h : Fin d → Option Bool) : negativeCount h ≤ signedSupport h := by
  exact Finset.sum_le_sum fun i _ => by
    cases hi : h i with
    | none => simp
    | some b => cases b <;> simp

private theorem patternSteps_mem {d l : ℕ} (hl : 1 ≤ l) (p : Pattern d l) :
    patternSteps d l p ∈ Fintype.piFinset (fun _ => box 1 (l+1) - box 1 (l+1)) := by
  let B := box 1 (l+1)
  have h0 : (0 : Lattice 1) ∈ B := Fintype.mem_piFinset.mpr fun _ => Finset.mem_Ico.mpr ⟨by simp,by simp⟩
  have h1 : (1 : Lattice 1) ∈ B := Fintype.mem_piFinset.mpr fun _ => Finset.mem_Ico.mpr ⟨by simp,by simp; omega⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  change (fun _ : Fin 1 => unitShift (patternCode p i)) ∈ B-B
  cases v : patternCode p i with
  | none => exact Finset.mem_sub.mpr ⟨0,h0,0,h0,by ext; simp [unitShift]⟩
  | some b =>
    cases b with
    | false => exact Finset.mem_sub.mpr ⟨0,h0,1,h1,by ext; simp [unitShift]⟩
    | true => exact Finset.mem_sub.mpr ⟨1,h1,0,h0,by ext; simp [unitShift]⟩

/-- Retaining precisely the signed-step configurations in the weighted test
gives the finite-dimensional inequality used for the entropy lower bound. -/
theorem signed_weightedEnergy_lower (d l p : ℕ) (hl : 1 ≤ l) (f : Lattice 1 → ℝ≥0) :
    (d.choose l * 2^l : ℕ) * ((binomialProduct f l 0)^(2^(d-l)))^p ≤
      weightedEnergy d p (box 1 (l+1)) f := by
  classical
  let B := box 1 (l+1)
  let H := fun h : Fin d → Lattice 1 => (∑ x ∈ B, finiteCubeProduct d f h x)^p
  let Z := (binomialProduct f l 0)^(2^(d-l))
  have lower (c : Pattern d l) : Z^p ≤ H (patternSteps d l c) := by
    let v := patternCode c
    let x : Lattice 1 := fun _ => negativeCount v
    have sx : x ∈ B := Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr ⟨by dsimp [x]; positivity,by
      have h := (negativeCount_le_support v).trans_eq (patternSupport c)
      change ((negativeCount v : ℕ):ℤ) < (l+1:ℕ); omega⟩
    have eq : finiteCubeProduct d f (patternSteps d l c) x = Z := by
      change finiteCubeProduct d f (fun i _ => unitShift (patternCode c i)) x = Z
      simpa only [x, Z, v, zero_add, patternSupport] using finiteCubeProduct_signed d f (patternCode c) 0
    exact pow_le_pow_left' (eq.ge.trans (Finset.single_le_sum (f := fun y => finiteCubeProduct d f (patternSteps d l c) y)
      (fun _ _ => zero_le) sx)) p
  change _ ≤ ∑ h ∈ Fintype.piFinset (fun _ : Fin d => B-B), H h
  calc
    _ = ∑ _c : Pattern d l, Z^p := by rw [Finset.sum_const, Finset.card_univ, patternCount, nsmul_eq_mul]
    _ ≤ ∑ c : Pattern d l, H (patternSteps d l c) := Finset.sum_le_sum fun c _ => lower c
    _ = ∑ h ∈ Finset.univ.map (patternSteps d l), H h := (Finset.sum_map _ _ _).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      rintro h hh; obtain ⟨c,_,rfl⟩ := Finset.mem_map.mp hh; exact patternSteps_mem hl c)
      (fun _ _ _ => zero_le)

end LpGowers.Discrete
