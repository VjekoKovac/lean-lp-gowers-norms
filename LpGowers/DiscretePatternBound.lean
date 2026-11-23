module

public import LpGowers.DiscretePatterns
public import LpGowers.DiscreteEntropyFactors

/-! # The finite pattern upper bound in Section 8 -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace LpGowers.Discrete

/-- Integer position of a vertex in a based pattern of active directions. -/
def patternPoint {l : ℕ} (z : (Fin l → Lattice 1) × Lattice 1) (s : Finset (Fin l)) : ℤ :=
  z.2 0 + ∑ i ∈ s, z.1 i 0

/-- Hölder's inequality on the bases contributes n^(p−1) in a lower layer.
The top layer has a unique base. -/
def patternCoefficient (N p l : ℕ) : ℝ≥0 := if l = N then 1 else (N+1:ℕ)^(p-1)

/-- Trial upper bound for the powered one-dimensional Gowers functional after
zero directions have been removed and the remaining patterns grouped. -/
def patternUpperSum (N p d : ℕ) (g : ℤ → ℝ≥0) (t : ℝ) : ℝ≥0 :=
  (∑ j ∈ Finset.Ico 0 ((N+1 : ℕ):ℤ), g j ^ (t/p))^p +
    ∑ l ∈ Finset.Icc 1 N, (d.choose l : ℝ≥0) * patternCoefficient N p l *
      ∑ z ∈ activePatterns (N+1) l, subsetMonomial l (patternPoint z) g t

theorem patternPoint_range {N l : ℕ} {z : (Fin l → Lattice 1) × Lattice 1}
    (hz : z∈activePatterns (N+1) l) (s : Finset (Fin l)) :
    patternPoint z s ∈ Finset.Ico 0 ((N+1:ℕ):ℤ) := by
  have hh := (Finset.mem_filter.mp hz).2 s
  simpa [patternPoint,Finset.sum_apply] using (Fintype.mem_piFinset.mp hh) 0

theorem patternEntropy_lower {N l : ℕ} {z : (Fin l → Lattice 1) × Lattice 1}
    (hz : z∈activePatterns (N+1) l) : binomialEntropy l ≤ subsetEntropy l (patternPoint z) := by
  apply binomialEntropy_le_signed
  intro i hi
  have hs := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
  have hne := Finset.ne_of_mem_erase (Fintype.mem_piFinset.mp hs.1 i)
  exact hne (funext fun j => by rw [Fin.eq_zero j]; exact hi)

theorem patternMonomial_entropy {N l : ℕ} {z : (Fin l → Lattice 1) × Lattice 1}
    (hz : z∈activePatterns (N+1) l) (g : ℤ → ℝ≥0)
    (hg : ∑ j ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g j = 1) (t : ℝ) (ht : 0 ≤ t) :
    (subsetMonomial l (patternPoint z) g t : ℝ) ≤ 2^(-binomialEntropy l*t) := by
  apply (subsetMonomial_entropy l _ g _ t ht).trans
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (neg_le_neg (patternEntropy_lower hz)) ht
  · rw [← hg]
    apply Finset.sum_le_sum_of_subset
    rintro j hj
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hj
    exact patternPoint_range hz s

end LpGowers.Discrete
