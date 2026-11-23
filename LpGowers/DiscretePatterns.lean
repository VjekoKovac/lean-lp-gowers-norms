module

public import LpGowers.DiscreteRegroup
import Mathlib.Tactic

/-! # Nonzero increment patterns fitting in an integer interval

The two vertices obtained by taking all negative or all positive steps give the
exact span. A fitting pattern has at most `n-1` active steps. Equality forces
every step to have absolute value one and uniquely determines the origin. -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Pointwise
namespace LpGowers.Discrete

/-- The finite alphabet of active increments on a side of length `n`. -/
def stepPool (n l : ℕ) : Finset (Fin l → Lattice 1) :=
  Fintype.piFinset (fun _ => (box 1 n - box 1 n).erase 0)

/-- Base-pointed patterns of active increments, independent of the full degree. -/
def activePatterns (n l : ℕ) : Finset ((Fin l → Lattice 1) × Lattice 1) :=
  (stepPool n l ×ˢ box 1 n).filter fun z => fits (box 1 n) z.1 z.2

/-- The mass on integer `j` of a translated sum of fair `{0,1}` bits. -/
def patternWeight {l : ℕ} (z : (Fin l → Lattice 1) × Lattice 1) (j : ℤ) : ℝ :=
  ((Finset.univ.filter fun S : Finset (Fin l) => z.2 0 + ∑ i ∈ S, z.1 i 0 = j).card : ℝ) / 2^l

theorem activeStep_ne_zero {n l : ℕ} {h : Fin l → Lattice 1} (hh : h ∈ stepPool n l) (i : Fin l) :
    h i 0 ≠ 0 := by
  have hv := (Finset.mem_erase.mp (Fintype.mem_piFinset.mp hh i)).1
  intro he
  apply hv
  funext j
  change h i j = 0
  rwa [Fin.eq_zero j]

private def negSum {l : ℕ} (h : Fin l → Lattice 1) : ℤ :=
  ∑ i, if h i 0 < 0 then h i 0 else 0

private def posSum {l : ℕ} (h : Fin l → Lattice 1) : ℤ :=
  ∑ i, if 0 < h i 0 then h i 0 else 0

private theorem span_identity {l : ℕ} (h : Fin l → Lattice 1) :
    (∑ i, |h i 0|) = posSum h - negSum h := by
  rw [posSum,negSum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (h i 0) 0 with H | H | H
  · simp [H,not_lt.mpr H.le,abs_of_neg H]
  · simp [H]
  · simp [H,not_lt.mpr H.le,abs_of_pos H]

private theorem span_endpoints {n l : ℕ} {h : Fin l → Lattice 1} {x : Lattice 1}
    (hx : fits (box 1 n) h x) :
    0 ≤ x 0 + negSum h ∧ x 0 + posSum h < (n:ℤ) := by
  have v (S : Finset (Fin l)) := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (hx S) 0)
  have vs (S : Finset (Fin l)) : 0 ≤ x 0 + ∑ i ∈ S,h i 0 ∧ x 0 + ∑ i ∈ S,h i 0 < (n:ℤ) := by
    simpa only [Pi.add_apply,Finset.sum_apply] using v S
  have hn := (vs (Finset.univ.filter fun i => h i 0 < 0)).1
  have hp := (vs (Finset.univ.filter fun i => 0 < h i 0)).2
  simpa only [negSum,posSum,Finset.sum_filter] using And.intro hn hp

/-- Only patterns of total absolute span strictly below the side length fit. -/
theorem pattern_span {n l : ℕ} {h : Fin l → Lattice 1} {x : Lattice 1}
    (hx : fits (box 1 n) h x) : ∑ i, |h i 0| < (n:ℤ) := by
  obtain ⟨hlo,hhi⟩ := span_endpoints hx
  rw [span_identity]
  omega

theorem active_count_le_span {n l : ℕ} {h : Fin l → Lattice 1} (hh : h ∈ stepPool n l) :
    (l:ℤ) ≤ ∑ i, |h i 0| := by
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => show 1 ≤ |h i 0| by
      have H := activeStep_ne_zero hh i
      rw [abs,max_def]; split <;> omega)

theorem leading_unit {l : ℕ} {h : Fin l → Lattice 1} {x : Lattice 1}
    (hh : h ∈ stepPool (l+1) l) (hx : fits (box 1 (l+1)) h x) (i : Fin l) :
    h i 0 = -1 ∨ h i 0 = 1 := by
  have H := pattern_span hx
  have hp (j : Fin l) : 0 ≤ |h j 0|-1 := by
    have Hj := activeStep_ne_zero hh j
    rw [abs,max_def]; split <;> omega
  have hsum : (∑ j, (|h j 0|-1)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hL := active_count_le_span hh
    omega
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j)).mp hsum i (Finset.mem_univ _)
  rw [abs,max_def] at he
  split at he <;> omega

theorem leading_origin {l : ℕ} {h : Fin l → Lattice 1} {x y : Lattice 1}
    (hh : h ∈ stepPool (l+1) l) (hx : fits (box 1 (l+1)) h x)
    (hy : fits (box 1 (l+1)) h y) : x = y := by
  have hl := active_count_le_span hh
  rw [span_identity] at hl
  obtain ⟨hx₀,hx₁⟩ := span_endpoints hx
  obtain ⟨hy₀,hy₁⟩ := span_endpoints hy
  ext i
  rw [Fin.eq_zero i]
  omega

/-- Left endpoint of the admissible bases for a full sequence of unit signs. -/
theorem signed_fitting_origin {l : ℕ} (b : Fin l → Bool) {x : Lattice 1}
    (hx : fits (box 1 (l+1)) (fun i _ => unitShift (some (b i))) x) :
    x = fun _ => ((negativeCount (fun i => some (b i)) : ℕ):ℤ) := by
  let h : Fin l → Lattice 1 := fun i _ => unitShift (some (b i))
  have hsum : posSum h - negSum h = (l:ℤ) := by
    rw [← span_identity]
    have ha (i : Fin l) : |h i 0| = 1 := by cases e : b i <;> norm_num [h,e,unitShift]
    simp [ha]
  have hn : negSum h = -((negativeCount (fun i => some (b i)) : ℕ):ℤ) := by
    simp only [negSum,negativeCount,Nat.cast_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [h]
    by_cases e : b i = true
    · simp [e,unitShift]
    · have he : b i = false := by simpa using e
      simp [he,unitShift]
  obtain ⟨lo,hi⟩ := span_endpoints hx
  change 0 ≤ x 0 + negSum h at lo
  change x 0 + posSum h < (l+1:ℕ) at hi
  ext i
  rw [Fin.eq_zero i]
  omega

end LpGowers.Discrete
