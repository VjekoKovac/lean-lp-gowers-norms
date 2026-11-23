module

public import LpGowers.DiscreteLeadingPattern
public import LpGowers.DiscretePatternBound
import Mathlib.Tactic

/-! # The normalized sum of pattern monomials bounds the lattice energy -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal Pointwise
namespace LpGowers.Discrete

/-- Evaluation at the only coordinate identifies the one-dimensional box with
the integer interval, without any ambient counting-measure factor. -/
theorem box_coordinate_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (v : ℤ → M) :
    (∑ x ∈ box 1 n, v (x 0)) = ∑ j ∈ Finset.Ico 0 (n:ℤ), v j := by
  apply Finset.sum_bij' (fun (x : Lattice 1) _ => x 0) (fun (j : ℤ) _ (_ : Fin 1) => j)
  · exact fun x hx => Fintype.mem_piFinset.mp hx 0
  · exact fun j hj => Fintype.mem_piFinset.mpr fun _ => hj
  · intro x _; funext i; rw [Fin.eq_zero i]
  · intros; rfl
  · intros; rfl

private theorem zero_rank {n d p : ℕ} (hp : 0<p) (t : ℝ) (g : ℤ → ℝ≥0) (f : Lattice 1 → ℝ≥0)
    (hf : ∀ x ∈ box 1 n, f x = g (x 0) ^ (t / ((2:ℝ)^d*p))) :
    activeSum (box 1 n) ((box 1 n-box 1 n).erase 0) p 0 d f =
      (∑ j ∈ Finset.Ico 0 (n:ℤ), g j ^ (t/p))^p := by
  have h (x : Lattice 1) (hx : x∈box 1 n) : (f x)^(2^d) = g (x 0)^(t/p) := by
    rw [hf x hx,← NNReal.rpow_mul_natCast]
    congr 1
    push_cast
    have hp' : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
  simp only [activeSum, finiteCubeProduct]
  have hE : (Fintype.piFinset (fun _ : Fin 0 => (box 1 n-box 1 n).erase 0)) = Finset.univ := by
    ext v
    simp only [Fintype.mem_piFinset,Finset.mem_univ,iff_true]
    intro i; exact i.elim0
  rw [hE,Fintype.sum_unique]
  congr 1
  rw [← box_coordinate_sum n (fun j => g j ^ (t/p))]
  exact Finset.sum_congr rfl h

/-- The one-dimensional finite energy after `f=g^(t/(2^d p))` lies below the
paper's finite-rank pattern expansion. The bound is uniform in the input and
retains exactly the top coefficient. -/
theorem weightedEnergy_le_patternUpperSum {N d p : ℕ} (hNd : N≤d) (hp : 0<p) (t : ℝ)
    (g : ℤ → ℝ≥0) (f : Lattice 1 → ℝ≥0) (hzero : ∀ x ∉ box 1 (N+1), f x=0)
    (hf : ∀ x ∈ box 1 (N+1), f x = g (x 0) ^ (t / ((2:ℝ)^d*p))) :
    weightedEnergy d p (box 1 (N+1)) f ≤ patternUpperSum N p d g t := by
  classical
  let A := box 1 (N+1)
  let F := fun l => (d.choose l : ℝ≥0) * activeSum A ((A-A).erase 0) p l (d-l) f
  have hA : A.Nonempty := ⟨0,Fintype.mem_piFinset.mpr (fun i => Finset.mem_Ico.mpr ⟨by simp,by simp⟩)⟩
  rw [weightedEnergy_regroup A hA d p]
  change (∑ l ∈ Finset.range (d+1), F l) ≤ _
  have trunc : (∑ l ∈ Finset.range (d+1), F l) = ∑ l ∈ Finset.range (N+1), F l := by
    apply (Finset.sum_subset (Finset.range_mono (by omega)) _).symm
    intro l _ hl
    unfold F
    rw [activeSum_vanish (show N+1≤l by simpa using hl) hp _ f hzero,mul_zero]
  have splitRange : Finset.range (N+1) = insert 0 (Finset.Icc 1 N) := by
    ext l
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [trunc,splitRange,Finset.sum_insert (by simp),patternUpperSum]
  gcongr ?_ + ?_
  · have H := zero_rank hp t g f hf (d:=d)
    simpa [F,A] using H.le
  · apply Finset.sum_le_sum
    intro l hl
    have hl' : l ≤ N := (Finset.mem_Icc.mp hl).2
    rw [mul_assoc]
    unfold F
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases he : l = N
    · subst l
      simpa [A,patternCoefficient,subsetMonomial,patternPoint] using
        (activeSum_leading N d p hNd hp t g f hzero hf).le
    · simpa [A,patternCoefficient,he,subsetMonomial,patternPoint] using
        activeSum_middle (hl'.trans hNd) hp t g f hzero hf

end LpGowers.Discrete
