module

public import LpGowers.Discrete
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! # Entropy of weighted independent fair bits

Beker, Crmarić and Kovač prove their Proposition 10 using majorization. We
apply Jensen's inequality directly to every antichain level set, using the
Lubell–Yamamoto–Meshalkin inequality from Mathlib. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace LpGowers.Discrete

/-- The entropy, in bits, of a random variable on the uniform discrete cube. -/
def subsetEntropy {Z : Type*} [DecidableEq Z] (l : ℕ) (F : Finset (Fin l) → Z) : ℝ :=
  (∑ z ∈ Finset.univ.image F,
    Real.negMulLog (((Finset.univ.filter (fun s => F s = z)).card : ℝ) / 2^l)) / Real.log 2

/-- An observable whose level sets are antichains has entropy at least that of
the symmetric binomial distribution. -/
theorem binomialEntropy_le_of_antichains {Z : Type*} [DecidableEq Z] (l : ℕ)
    (F : Finset (Fin l) → Z) (hF : ∀ z, IsAntichain (· ⊆ ·) {s | F s = z}) :
    binomialEntropy l ≤ subsetEntropy l F := by
  classical
  let b (k : ℕ) : ℝ := (l.choose k : ℝ)
  let a (k : ℕ) := b k/(2:ℝ)^l
  let fiber (z : Z) := Finset.univ.filter fun s => F s = z
  let w (s : Finset (Fin l)) := (b s.card)⁻¹
  have hb (k : ℕ) (hk : k ≤ l) : 0 < b k := by dsimp [b]; exact_mod_cast Nat.choose_pos hk
  have hw (s : Finset (Fin l)) : 0 < w s :=
    inv_pos.mpr (hb s.card (by simpa using s.card_le_univ))
  have hrow (z : Z) : ∑ s ∈ fiber z, w s ≤ 1 := by
    have hh : IsAntichain (fun a b : Finset (Fin l) => a ⊆ b) (fiber z : Set (Finset (Fin l))) := by
      simpa [fiber] using hF z
    simpa [w,b] using (Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℝ) hh)
  have hcell (z : Z) : ∑ s ∈ fiber z, w s * Real.negMulLog (a s.card) ≤
      Real.negMulLog (((fiber z).card : ℝ)/2^l) := by
    have hJ := Real.concaveOn_negMulLog.map_add_sum_le (t := fiber z) (w := w)
      (v := 1-∑ s ∈ fiber z, w s) (p := fun s => a s.card) (q := 0)
      (fun s _ => (hw s).le) (by ring) (fun s _ => show 0 ≤ a s.card by dsimp [a,b]; positivity)
      (sub_nonneg.mpr (hrow z)) (by simp)
    have he (s : Finset (Fin l)) : w s * a s.card = 1/(2:ℝ)^l := by
      dsimp [w,a]
      field_simp [(hb _ (by simpa using s.card_le_univ)).ne']
    simpa [smul_eq_mul, he, div_eq_mul_inv] using hJ
  have htotal := Finset.sum_le_sum (s := Finset.univ.image F) fun z _ => hcell z
  have hgroup : ∑ z ∈ Finset.univ.image F, ∑ s ∈ fiber z, w s * Real.negMulLog (a s.card) =
      ∑ s, w s * Real.negMulLog (a s.card) := by
    apply Finset.sum_fiberwise_of_maps_to
    simp
  rw [hgroup] at htotal
  have hlayer (k : ℕ) : (Finset.univ.filter fun s : Finset (Fin l) => s.card=k) = Finset.univ.powersetCard k := by
    ext; simp
  have hsum : ∑ s : Finset (Fin l), w s * Real.negMulLog (a s.card) =
      ∑ k ∈ Finset.range (l+1), Real.negMulLog (a k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (f := fun s : Finset (Fin l) => w s * Real.negMulLog (a s.card))
      (t := Finset.range (l+1)) (g := Finset.card) (by intro s hs; simp; simpa using s.card_le_univ)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ l := by simpa using hk
    calc
      _ = ∑ _ ∈ (Finset.univ.filter fun s : Finset (Fin l) => s.card=k), (b k)⁻¹*Real.negMulLog (a k) :=
        Finset.sum_congr rfl (fun s hs => by simp [w,(Finset.mem_filter.mp hs).2])
      _ = _ := by simp [hlayer,b, (Nat.choose_pos hk').ne']
  rw [hsum] at htotal
  have hBin : binomialEntropy l = (∑ k ∈ Finset.range (l+1), Real.negMulLog (a k)) / Real.log 2 := by
    simp [binomialEntropy, a, b, logTwo, Real.logb, Real.negMulLog]
    rw [neg_div, Finset.sum_div]
    simp [mul_div_assoc]
  rw [hBin, subsetEntropy]
  exact div_le_div_of_nonneg_right htotal (Real.log_nonneg (by norm_num))

/-- Beker–Crmarić–Kovač, Proposition 10, for strictly positive steps. -/
theorem binomialEntropy_le_subsetSum (l : ℕ) (h : Fin l → ℤ) (hh : ∀ i, 0 < h i) :
    binomialEntropy l ≤ subsetEntropy l (fun s => ∑ i ∈ s, h i) := by
  apply binomialEntropy_le_of_antichains
  intro z s hs t ht hst hsub
  obtain ⟨i,hit,his⟩ := Finset.not_subset.mp (show ¬ t ⊆ s by intro h; exact hst (Finset.Subset.antisymm hsub h))
  have H := Finset.sum_lt_sum_of_subset hsub hit his (hh i) (fun j _ _ => (hh j).le)
  exact (ne_of_lt H) (hs.trans ht.symm)



/-- Entropy is invariant under bijections of the uniform sample space and
under injective relabeling of the values. -/
theorem subsetEntropy_relabel {Z W : Type*} [DecidableEq Z] [DecidableEq W] (l : ℕ)
    (F : Finset (Fin l) → Z) (e : Equiv.Perm (Finset (Fin l))) (v : Z ↪ W) :
    subsetEntropy l (fun s => v (F (e s))) = subsetEntropy l F := by
  classical
  have hs : Finset.univ.image (fun s => v (F (e s))) = (Finset.univ.image F).map v := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨s,rfl⟩; exact ⟨F (e s), ⟨e s,rfl⟩, rfl⟩
    · rintro ⟨_,⟨s,rfl⟩,rfl⟩; exact ⟨e.symm s, by simp⟩
  have hcard (z : Z) :
      (Finset.univ.filter fun s => v (F (e s)) = v z).card =
        (Finset.univ.filter fun s => F s = z).card := by
    rw [← Finset.card_map e.toEmbedding]
    congr 1
    ext s
    simp [Finset.mem_map_equiv]
  simp only [subsetEntropy, hs, Finset.sum_map, hcard]

/-- Proposition 10 of Beker–Crmarić–Kovač, for arbitrary nonzero signed
integer weights and integer translation. -/
theorem binomialEntropy_le_signed (l : ℕ) (h : Fin l → ℤ) (hh : ∀ i, h i ≠ 0) (x : ℤ) :
    binomialEntropy l ≤ subsetEntropy l (fun s => x + ∑ i ∈ s, h i) := by
  let flip (s : Finset (Fin l)) : Finset (Fin l) :=
    Finset.univ.filter (fun i => if h i < 0 then i ∉ s else i ∈ s)
  have hflip : Function.Involutive flip := by
    intro s
    ext i
    by_cases hi : h i<0 <;> simp [flip,hi]
  let e := hflip.toPerm flip
  let N := ∑ i : Fin l, if h i<0 then |h i| else 0
  let v : ℤ ↪ ℤ := ⟨fun a => x+a-N, by intro a b he; dsimp at he; omega⟩
  have hr (s : Finset (Fin l)) :
      x + ∑ i ∈ s, h i = v (∑ i ∈ e s, |h i|) := by
    change _ = x + (∑ i ∈ flip s, |h i|)-N
    suffices (∑ i ∈ s, h i) = (∑ i ∈ flip s, |h i|)-N by linarith
    rw [show (∑ i ∈ s, h i) = ∑ i : Fin l, if i ∈ s then h i else 0 by simp]
    dsimp [N,flip]
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : h i < 0
    · by_cases hs : i∈s <;> simp [hi,hs,abs_of_neg hi]
    · by_cases hs : i∈s <;> simp [hi,hs,abs_of_nonneg (le_of_not_gt hi)]
  rw [show (fun s => x + ∑ i ∈ s, h i) = fun s => v (∑ i ∈ e s, |h i|) by funext s; exact hr s]
  rw [subsetEntropy_relabel l (fun s => ∑ i ∈ s, |h i|) e v]
  exact binomialEntropy_le_subsetSum l _ (fun i => abs_pos.mpr (hh i))

end LpGowers.Discrete
