module

public import LpGowers.DiscreteEntropyFactors
public import LpGowers.DiscretePatterns
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! # Concentration at one atom in the large-degree cube estimate

The zero-increment contribution is bounded by the collision probability
of the normalized input. Every nonzero pattern contains two different lattice
points, at least one outside the distinguished atom. Their product is bounded
by the complementary collision probability, giving the last case of §8. -/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace LpGowers.Discrete

private def offMass (I : Finset ℤ) (g : ℤ → ℝ≥0) : ℝ≥0 :=
  ∑ i ∈ I, g i * ∑ j ∈ I.erase i, g j

private theorem collision_off (I : Finset ℤ) (g : ℤ → ℝ≥0) (hg : ∑ j ∈ I, g j = 1) :
    (∑ j ∈ I, (g j)^2) + offMass I g = 1 := by
  rw [offMass, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ I, g i * ∑ j ∈ I, g j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq, ← mul_add, add_comm (g i), Finset.sum_erase_add _ _ hi]
    _ = _ := by simp [hg]

private theorem pair_le_off (I : Finset ℤ) (g : ℤ → ℝ≥0) {i j : ℤ}
    (hi : i∈I) (hj : j∈I) (hne : i≠j) : g i*g j ≤ offMass I g := by
  have hl : g j ≤ ∑ s ∈ I.erase i, g s :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_erase.mpr ⟨hne.symm,hj⟩)
  apply (mul_le_mul_of_nonneg_left hl (zero_le)).trans
  exact Finset.single_le_sum (f := fun y => g y * ∑ z ∈ I.erase y, g z) (fun _ _ => zero_le) hi

/-- For a probability vector, concentration above `1-θ` at one index bounds
all other entries by `θ`. -/
theorem small_outside_peak (I : Finset ℤ) (g : ℤ → ℝ≥0) {x : ℤ} (hx : x∈I)
    (hg : ∑ j ∈ I, g j = 1) {θ : ℝ≥0} (hpeak : 1-θ ≤ g x) :
    ∀ y ∈ I, y≠x → g y≤θ := by
  intro y hy hxy
  have h : g y ≤ ∑ z ∈ I.erase x, g z := Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_erase.mpr ⟨hxy,hy⟩)
  have hsum := Finset.sum_erase_add (s:=I) g hx
  rw [hg] at hsum
  have hpeak' : 1≤g x+θ := tsub_le_iff_right.mp hpeak
  exact le_of_add_le_add_right ((add_le_add_left h (g x)).trans (hsum.le.trans (by simpa [add_comm] using hpeak')))

private def patVertex {l : ℕ} (z : (Fin l → Lattice 1) × Lattice 1) (s : Finset (Fin l)) : ℤ :=
  z.2 0 + ∑ i ∈ s, z.1 i 0

private theorem concentrated_pattern {n l N : ℕ} (hl : 1≤l) (hlN : l≤N)
    {z : (Fin l → Lattice 1) × Lattice 1} (hz : z∈activePatterns n l)
    (g : ℤ → ℝ≥0) (hg : ∑ j ∈ Finset.Ico (0:ℤ) n, g j = 1) {j₀ : ℤ}
    {θ : ℝ≥0} (hθ₀ : 0<θ) (hθ : θ≤1) (hsmall : ∀ j ∈ Finset.Ico (0:ℤ) n, j≠j₀ → g j≤θ)
    {t : ℝ} (ht : 1 ≤ t / 2^N) :
    subsetMonomial l (patVertex z) g t ≤ offMass (Finset.Ico 0 n) g * θ^(t/2^N-1) := by
  let I := Finset.Ico (0:ℤ) n
  let V := patVertex z
  have hp := Finset.mem_filter.mp hz
  obtain ⟨hh,hx⟩ := Finset.mem_product.mp hp.1
  have hfit := hp.2
  have inside (s : Finset (Fin l)) : V s ∈ I := by
    simpa [V,patVertex,I,Finset.sum_apply] using (Fintype.mem_piFinset.mp (hfit s) 0)
  have h1 (s) : g (V s) ≤ 1 := (Finset.single_le_sum (fun _ _ => zero_le) (inside s)).trans_eq hg
  let i : Fin l := ⟨0,by omega⟩
  have hn : z.1 i 0 ≠ 0 := by
    have he := (Finset.mem_erase.mp (Fintype.mem_piFinset.mp hh i)).1
    intro hz
    apply he
    funext k
    change z.1 i k = 0
    rwa [Fin.eq_zero k]
  have hd : V ∅ ≠ V {i} := by simp [V,patVertex,hn]
  have htu : 0≤t := by
    have hb : 0<(2:ℝ)^N := by positivity
    linarith only [(le_div_iff₀ hb).mp ht,hb]
  have hT : t/2^N ≤ t/2^l := div_le_div_of_nonneg_left htu (by positivity)
    (pow_le_pow_right₀ (by norm_num) hlN)
  have hpow : θ^(t/2^l-1) ≤ θ^(t/2^N-1) :=
    NNReal.rpow_le_rpow_of_exponent_ge hθ₀ hθ (sub_le_sub_right hT 1)
  have bound (s u : Finset (Fin l)) (hne : V s≠V u) (hu : V u≠j₀) :
      subsetMonomial l V g t ≤ offMass I g * θ^(t/2^N-1) := by
    have h := subsetMonomial_concentrated l V g s u (fun h => hne (congrArg V h)) h1 t θ
      (hsmall _ (inside u) hu) (ht.trans hT)
    exact h.trans (mul_le_mul (pair_le_off I g (inside s) (inside u) hne) hpow (zero_le) (zero_le))
  by_cases h0 : V ∅ = j₀
  · exact bound ∅ {i} hd (fun h => hd (h0.trans h.symm))
  · exact bound {i} ∅ hd.symm h0

/-- The concentration case in the final paragraph of §8. The numerical rate
hypothesis uses a finite coefficient independent of the full degree. -/
theorem concentrated_patterns_le_one (n N d p : ℕ) (hd : 1≤d) (hp : 1≤p)
    (g : ℤ → ℝ≥0) (b : ℕ → ℝ≥0) (t : ℝ) {θ : ℝ≥0} (hθ₀ : 0<θ) (hθ : θ≤1)
    (hg : ∑ j ∈ Finset.Ico (0:ℤ) n, g j = 1) (j₀ : ℤ)
    (hsmall : ∀ j ∈ Finset.Ico (0:ℤ) n, j≠j₀ → g j≤θ)
    (hzero : 2≤t/p) (ht : 1≤t/2^N)
    (hrate : (∑ l ∈ Finset.Icc 1 N, b l * (activePatterns n l).card) *
      (d:ℝ≥0)^N * θ^(t/2^N-1) ≤1) :
    (∑ j ∈ Finset.Ico (0:ℤ) n, g j^(t/p))^p +
       ∑ l∈Finset.Icc 1 N, (d.choose l:ℝ≥0)*b l*
         ∑ z∈activePatterns n l, subsetMonomial l (fun s => z.2 0 + ∑ i∈s,z.1 i 0) g t ≤ 1 := by
  let I := Finset.Ico (0:ℤ) n
  let P := ∑ j ∈ I, (g j)^2
  let W := offMass I g
  let r := θ^(t/2^N-1)
  let L := Finset.Icc 1 N
  have hcollision : P+W=1 := collision_off I g hg
  have hsump : P ≤ 1 := le_self_add.trans_eq hcollision
  have hsing (j : ℤ) (hj : j∈I) : g j ≤ 1 :=
    (Finset.single_le_sum (fun _ _ => zero_le) hj).trans_eq hg
  have h0 : ∑ j ∈ I, g j^(t/p) ≤ P := by
    apply Finset.sum_le_sum; intro j hj
    have := Real.rpow_le_rpow_of_exponent_ge' (g j).coe_nonneg (show (g j:ℝ)≤1 by exact_mod_cast hsing j hj)
        (by norm_num : (0:ℝ)≤2) hzero
    exact_mod_cast (by simpa using this : (g j:ℝ)^(t/p) ≤ (g j:ℝ)^2)
  have h0' : (∑ j ∈ I, g j^(t/p))^p ≤ P := by
    apply le_trans _ h0
    have h := NNReal.rpow_le_self_of_le_one (h0.trans hsump) (show (1:ℝ)≤p by exact_mod_cast hp)
    simpa using h
  let mon (l : ℕ) (z : (Fin l → Lattice 1) × Lattice 1) := subsetMonomial l (patVertex z) g t
  have hterm (l : ℕ) (hl : l∈L) : (d.choose l:ℝ≥0)*b l*∑ z∈activePatterns n l, mon l z ≤
      b l*(activePatterns n l).card * ((d:ℝ≥0)^N * r)*W := by
    obtain ⟨hl₁,hl₂⟩ := Finset.mem_Icc.mp hl
    have hmon (z) (hz : z∈activePatterns n l) : mon l z ≤ W*r :=
      concentrated_pattern hl₁ hl₂ hz g hg hθ₀ hθ hsmall ht
    have hsum := Finset.sum_le_sum hmon
    rw [Finset.sum_const,nsmul_eq_mul] at hsum
    have hchoose : (d.choose l:ℝ≥0) ≤ (d:ℝ≥0)^N := by
      exact_mod_cast (Nat.choose_le_pow d l).trans (Nat.pow_le_pow_right hd hl₂)
    calc
      _ ≤ (d:ℝ≥0)^N*b l*((activePatterns n l).card*(W*r)) := by gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  simp_rw [← Finset.sum_mul] at hsum
  change _ + (∑ l∈L, (d.choose l:ℝ≥0)*b l*∑ z∈activePatterns n l, mon l z) ≤ 1
  apply (add_le_add h0' hsum).trans
  rw [← hcollision]
  apply add_le_add_right
  have H : (∑ l∈L,b l * (activePatterns n l).card) * ((d:ℝ≥0)^N*r) ≤ 1 := by
    simpa only [mul_assoc] using hrate
  exact (mul_le_mul_of_nonneg_right H (zero_le)).trans_eq (one_mul _)

end LpGowers.Discrete
