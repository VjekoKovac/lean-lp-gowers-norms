module

public import LpGowers.Discrete
public import Mathlib.Tactic

/-! Proofs from the discrete-cube argument in §8 of arXiv:2609.08916v2. -/
@[expose] public section

noncomputable section

open scoped BigOperators Pointwise
namespace LpGowers.Discrete

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- At most one cube with prescribed increments starts at each member of A. -/
theorem baseCount_le_card {d : ℕ} (A : Finset G) (h : Fin d → G) :
    baseCount A h ≤ A.card :=
  Finset.card_filter_le _ _

/-- The term for the zero tuple is exactly the cardinality of A. -/
theorem baseCount_zero (d : ℕ) (A : Finset G) :
    baseCount A (0 : Fin d → G) = A.card := by
  simp [baseCount]

/-- Restricting the sum to coordinatewise differences loses no nonzero base count. -/
theorem baseCount_eq_zero_outside {d : ℕ} (A : Finset G) (h : Fin d → G)
    (hout : h ∉ Fintype.piFinset (fun _ : Fin d => A - A)) : baseCount A h = 0 := by
  by_contra hn
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨hxA, hc⟩ := Finset.mem_filter.mp hx
  apply hout
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : x + h i ∈ A := by simpa using hc {i}
  exact Finset.mem_sub.mpr ⟨x + h i, hi, x, hxA, by abel⟩

/-- The reduction to p=1 used for the upper bound in Theorem 1.5(b).
Here the paper's positive integer p is written k+1. -/
theorem energy_le_card_pow_mul (d k : ℕ) (A : Finset G) :
    energy d (k + 1) A ≤ A.card ^ k * energy d 1 A := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [pow_succ, pow_one]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (baseCount_le_card A h) k)

/-- Every exponent admissible at p=1 gives an explicit admissible exponent at
p=k+1, uniformly in m and n. -/
theorem setExponent_shift {d n : ℕ} (k : ℕ) {t : ℝ}
    (ht : t ∈ setExponents d 1 n) : t + k ∈ setExponents d (k + 1) n := by
  obtain ⟨hpos, hsmall⟩ := ht
  refine ⟨by positivity, ?_⟩
  intro m A hA
  calc
    (energy d (k + 1) A : ℝ) ≤ (A.card : ℝ) ^ k * (energy d 1 A : ℝ) := by
      exact_mod_cast energy_le_card_pow_mul d k A
    _ ≤ (A.card : ℝ) ^ k * (A.card : ℝ) ^ t := by
      exact mul_le_mul_of_nonneg_left (hsmall m A hA) (by positivity)
    _ = (A.card : ℝ) ^ (t + k) := by
      rw [Real.rpow_add_natCast' (by positivity) (by positivity : t + (k : ℝ) ≠ 0)]
      exact mul_comm _ _


/-- At fixed x, the d neighboring vertices x+hᵢ determine the increments.
Counting only these neighbors gives the dimension-free elementary bound at p=1. -/
theorem energy_one_le_card_pow (d : ℕ) (A : Finset G) :
    energy d 1 A ≤ A.card ^ (d + 1) := by
  classical
  let H := Fintype.piFinset (fun _ : Fin d => A - A)
  let valid (h : Fin d → G) (x : G) := ∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ A
  have hfixed (x : G) : (H.filter fun h => valid h x).card ≤ A.card ^ d := by
    rw [← Fintype.card_piFinset_const]
    apply Finset.card_le_card_of_injOn (fun h i => x + h i)
    · intro h hh
      apply Fintype.mem_piFinset.mpr
      intro i
      have hc := (Finset.mem_filter.mp hh).2
      simpa using hc {i}
    · intro h _ k _ heq
      funext i
      exact add_left_cancel (congrFun heq i)
  calc
    energy d 1 A = ∑ h ∈ H, ∑ x ∈ A, if valid h x then 1 else 0 := by
      simp [energy, H, valid, baseCount]
    _ = ∑ x ∈ A, ∑ h ∈ H, if valid h x then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ x ∈ A, A.card ^ d := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Finset.sum_boole, Nat.cast_id] using hfixed x
    _ = A.card ^ (d + 1) := by simp [pow_succ, Nat.mul_comm]

/-- The coarse exponent t=d+p used to start the large-side asymptotic. -/
theorem energy_le_card_pow_add (d k : ℕ) (A : Finset G) :
    energy d (k + 1) A ≤ A.card ^ (d + (k + 1)) := by
  calc
    energy d (k + 1) A ≤ A.card ^ k * energy d 1 A := energy_le_card_pow_mul d k A
    _ ≤ A.card ^ k * A.card ^ (d + 1) :=
      Nat.mul_le_mul_left _ (energy_one_le_card_pow d A)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The set of admissible energy exponents is nonempty, in every dimension. -/
theorem add_mem_setExponents (d k n : ℕ) :
    (((d + (k + 1) : ℕ) : ℝ)) ∈ setExponents d (k + 1) n := by
  refine ⟨by positivity, ?_⟩
  intro m A _
  rw [Real.rpow_natCast]
  exact_mod_cast energy_le_card_pow_add d k A

theorem criticalT_le_add (d k n : ℕ) :
    criticalT d (k + 1) n ≤ (d + (k + 1) : ℕ) := by
  exact csInf_le ⟨0, fun t ht => le_of_lt ht.1⟩ (add_mem_setExponents d k n)


/-- The exponent comparison used on the upper side of (1.13). -/
theorem criticalT_le_shift (d k n : ℕ) :
    criticalT d (k + 1) n ≤ criticalT d 1 n + k := by
  apply sub_le_iff_le_add.mp
  apply le_csInf ⟨_, add_mem_setExponents d 0 n⟩
  intro t ht
  apply sub_le_iff_le_add.mpr
  exact csInf_le ⟨0, fun u hu => le_of_lt hu.1⟩ (setExponent_shift k ht)

private def binaryPair : Finset (Lattice 1) := {0, 1}

private theorem card_binaryPair : binaryPair.card = 2 := by
  simp [binaryPair, zero_ne_one]

private theorem binaryPair_subset : binaryPair ⊆ box 1 2 := by
  intro x hx
  rcases Finset.mem_insert.mp hx with h | h
  · subst x; simp [box, Fintype.mem_piFinset]
  · have := Finset.mem_singleton.mp h
    subst x; simp [box, Fintype.mem_piFinset]

private def signedStep {d : ℕ} (u : Fin d × Bool) (j : Fin d) : Lattice 1 :=
  if j = u.1 then (if u.2 then 1 else -1) else 0

private theorem signedStep_injective (d : ℕ) :
    Function.Injective (signedStep (d := d)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ heq
  have hs := congrFun (congrFun heq i) (0 : Fin 1)
  by_cases h : i = j
  · subst j
    cases b <;> cases c <;> first | rfl | norm_num [signedStep] at hs
  · cases b <;> simp [signedStep, h] at hs

private theorem signedStep_ne_zero {d : ℕ} (u : Fin d × Bool) : signedStep u ≠ 0 := by
  rcases u with ⟨i, b⟩
  intro h
  have hs := congrFun (congrFun h i) (0 : Fin 1)
  cases b <;> norm_num [signedStep] at hs

private theorem baseCount_signedStep_pos {d : ℕ} (u : Fin d × Bool) :
    0 < baseCount binaryPair (signedStep u) := by
  rcases u with ⟨i, b⟩
  apply Finset.card_pos.mpr
  refine ⟨if b then 0 else 1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · cases b <;> simp [binaryPair]
  · intro s
    by_cases hi : i ∈ s <;> cases b <;> simp [binaryPair, signedStep, hi]

private theorem coord_ext {x y : Lattice 1} (h : x 0 = y 0) : x = y := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using h

private theorem binaryPair_mem {z : Lattice 1} : z ∈ binaryPair ↔ z 0 = 0 ∨ z 0 = 1 := by
  simp only [binaryPair, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · exact Or.inl (coord_ext h)
    · exact Or.inr (coord_ext h)

/-- A valid nonconstant cube on the full binary interval uses only one direction. -/
private theorem increments_of_pos {d : ℕ} {h : Fin d → Lattice 1}
    (hpos : 0 < baseCount binaryPair h) (hn : h ≠ 0) :
    ∃ u : Fin d × Bool, h = signedStep u := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
  obtain ⟨i, hi⟩ : ∃ i, h i 0 ≠ 0 := by
    by_contra! hall
    exact hn (funext fun j => coord_ext (hall j))
  have hs (s : Finset (Fin d)) :
      x 0 + ∑ j ∈ s, h j 0 = 0 ∨ x 0 + ∑ j ∈ s, h j 0 = 1 := by
    simpa [Finset.sum_apply] using binaryPair_mem.mp (hc s)
  have hi' := hs {i}
  simp only [Finset.sum_singleton] at hi'
  have hx' := binaryPair_mem.mp hx
  let b := decide (x 0 = 0)
  refine ⟨(i,b), ?_⟩
  funext j
  apply coord_ext
  by_cases hij : j = i
  · subst j
    by_cases hx0 : x 0 = 0 <;> simp [signedStep, b, hx0] <;> omega
  · have hj := hs {j}
    have hij' := hs {i,j}
    simp only [Finset.sum_singleton] at hj
    simp [Ne.symm hij] at hij'
    simp [signedStep, hij]
    omega

private theorem baseCount_signedStep (d : ℕ) (u : Fin d × Bool) :
    baseCount binaryPair (signedStep u) = 1 := by
  apply Nat.le_antisymm _ (baseCount_signedStep_pos u)
  rcases u with ⟨i, b⟩
  let x₀ : Lattice 1 := if b then 0 else 1
  calc
    baseCount binaryPair (signedStep (i,b)) ≤ ({x₀} : Finset (Lattice 1)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
      have hx' := binaryPair_mem.mp hx
      have hs := binaryPair_mem.mp (hc {i})
      apply Finset.mem_singleton.mpr
      apply coord_ext
      cases b <;> simp [signedStep, x₀] at hs ⊢ <;> omega
    _ = 1 := Finset.card_singleton _

/-- Exact energy of the full one-dimensional binary cube. Zero increments give
2^p ordered base-point choices. Each signed single direction gives one more. -/
theorem binary_energy (d k : ℕ) :
    energy d (k + 1) ({0, 1} : Finset (Lattice 1)) = 2 ^ (k + 1) + 2 * d := by
  let B : Finset (Fin d → Lattice 1) := Finset.univ.image signedStep
  have hB (h : Fin d → Lattice 1) (hh : h ∈ B) : 0 < baseCount binaryPair h := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hh
    exact baseCount_signedStep_pos u
  have hz : (0 : Fin d → Lattice 1) ∉ B := by
    intro hh
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hh
    exact signedStep_ne_zero u hu
  have hcard : B.card = 2 * d := by
    simp [B, Finset.card_image_of_injective _ (signedStep_injective d), Nat.mul_comm]
  have hsub : insert (0 : Fin d → Lattice 1) B ⊆
      Fintype.piFinset (fun _ : Fin d => binaryPair - binaryPair) := by
    intro h hh
    by_contra hout
    have hzero := baseCount_eq_zero_outside binaryPair h hout
    rcases Finset.mem_insert.mp hh with rfl | hh
    · simp [baseCount_zero, card_binaryPair] at hzero
    · exact (hB h hh).ne' hzero
  calc
    energy d (k + 1) binaryPair =
        ∑ h ∈ insert (0 : Fin d → Lattice 1) B, (baseCount binaryPair h) ^ (k + 1) := by
      apply Eq.symm
      apply Finset.sum_subset hsub
      intro h _ hh
      have hzero : baseCount binaryPair h = 0 := by
        by_contra hn
        obtain ⟨u, rfl⟩ := increments_of_pos (Nat.pos_of_ne_zero hn)
          (fun heq => hh (heq ▸ Finset.mem_insert_self _ _))
        exact hh (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩))
      simp [hzero]
    _ = (baseCount binaryPair (0 : Fin d → Lattice 1)) ^ (k + 1) + ∑ _ ∈ B, 1 := by
      rw [Finset.sum_insert hz]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hh
      simp [baseCount_signedStep]
    _ = 2 ^ (k + 1) + 2 * d := by simp [baseCount_zero, card_binaryPair, hcard]

/-- Sharpness direction of the first formula in Theorem 1.5(a). -/
theorem binary_criticalT_lower (d k : ℕ) :
    logTwo ((2 : ℝ) ^ (k + 1) + 2 * d) ≤ criticalT d (k + 1) 2 := by
  apply le_csInf ⟨_, add_mem_setExponents d k 2⟩
  intro t ht
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mpr
  obtain ⟨_, ht⟩ := ht
  have htest := ht 1 binaryPair binaryPair_subset
  rw [card_binaryPair] at htest
  refine le_trans ?_ htest
  exact_mod_cast (binary_energy d k).symm.le


/-- The integer cube has n^m points (also when m=0). -/
theorem card_box (m n : ℕ) : (box m n).card = n ^ m := by
  simp [box, Int.card_Ico]

/-- Use nonnegative increments and bases smaller than N inside an interval
of length n. This is the full-interval test at the start of the proof of (b). -/
theorem interval_energy_lower (d p N n : ℕ) (hN : (d + 1) * N ≤ n) :
    N ^ (d + p) ≤ energy d p (box 1 n) := by
  classical
  let I := box 1 N
  let A := box 1 n
  let H := Fintype.piFinset (fun _ : Fin d => I)
  have hsmall : N ≤ n := by nlinarith
  have hI : I ⊆ A := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro u
    have ⟨h₁, h₂⟩ := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp hx) u)
    exact Finset.mem_Ico.mpr ⟨h₁, h₂.trans_le (by exact_mod_cast hsmall)⟩
  have hverts (h : Fin d → Lattice 1) (hh : h ∈ H) :
      N ≤ baseCount A h := by
    have hcard : I.card = N := by simp [I, card_box]
    rw [← hcard]
    apply Finset.card_le_card
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hI hx, ?_⟩
    intro s
    apply Fintype.mem_piFinset.mpr
    intro u
    obtain ⟨hx₀, hx₁⟩ := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp hx) u)
    have hj (i : Fin d) : 0 ≤ h i u ∧ h i u < (N : ℤ) :=
      Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hh i) u)
    apply Finset.mem_Ico.mpr
    simp only [Pi.add_apply, Finset.sum_apply]
    constructor
    · exact add_nonneg hx₀ (Finset.sum_nonneg (fun j _ => (hj j).1))
    · have hsum : ∑ j ∈ s, h j u ≤ (d : ℤ) * N := by
        calc
          ∑ j ∈ s, h j u ≤ ∑ _ ∈ s, (N : ℤ) :=
            Finset.sum_le_sum (fun j _ => (hj j).2.le)
          _ = (s.card : ℤ) * N := by simp
          _ ≤ (d : ℤ) * N := by
            gcongr
            exact_mod_cast (show s.card ≤ d by simpa using Finset.card_le_univ s)
      have hn' : ((d : ℤ) + 1) * N ≤ n := by exact_mod_cast hN
      linarith
  by_cases hpos : N = 0
  · subst N
    by_cases hdeg : d + p = 0
    · have hd : d = 0 := by omega
      have hp : p = 0 := by omega
      subst d; subst p; simp [energy]
    · simp [Nat.zero_pow (Nat.pos_of_ne_zero hdeg)]
  have hsub : H ⊆ Fintype.piFinset (fun _ : Fin d => A - A) := by
    intro h hh
    by_contra hout
    have hzero := baseCount_eq_zero_outside A h hout
    have hlow := hverts h hh
    omega
  calc
    N ^ (d + p) = ∑ _ ∈ H, N ^ p := by simp [H, I, card_box, pow_add]
    _ ≤ ∑ h ∈ H, (baseCount A h) ^ p :=
      Finset.sum_le_sum (fun h hh => Nat.pow_le_pow_left (hverts h hh) p)
    _ ≤ energy d p A := Finset.sum_le_sum_of_subset hsub

/-- Quantitative version of the first step of the paper's large-side argument:
the explicit loss below is of order 1/log n. -/
theorem largeSide_coarse_lower (d k n : ℕ) (hn : 2 * (d + 1) ≤ n) :
    ((d + (k + 1) : ℕ) : ℝ) -
        (d + (k + 1) : ℕ) * Real.log (2 * ((d : ℝ) + 1)) / Real.log n ≤
      criticalT d (k + 1) n := by
  let N := n / (d + 1)
  let D : ℕ := d + (k + 1)
  have hN : (d + 1) * N ≤ n := Nat.mul_div_le _ _
  have hNpos : 0 < N := Nat.div_pos (by omega) (by omega)
  have hn' : n ≤ 2 * (d + 1) * N := by
    have h := Nat.mod_lt n (by omega : 0 < d + 1)
    have h' := Nat.mod_add_div n (d + 1)
    change _ ≤ _ * (n / (d + 1))
    have : 1 ≤ n / (d + 1) := hNpos
    nlinarith [Nat.mul_le_mul_left (d + 1) this]
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hlog : Real.log n ≤ Real.log (2 * ((d : ℝ) + 1)) + Real.log N := by
    rw [← Real.log_mul (by positivity) hNreal.ne']
    exact Real.log_le_log (by linarith) (by exact_mod_cast hn')
  apply le_csInf ⟨_, add_mem_setExponents d k n⟩
  intro t ht
  have htest := ht.2 1 (box 1 n) (Finset.Subset.refl _)
  rw [card_box, pow_one] at htest
  have htest' : (N : ℝ) ^ D ≤ (n : ℝ) ^ t :=
    le_trans (by exact_mod_cast interval_energy_lower d (k + 1) N n hN) htest
  have hlog' := Real.log_le_log (pow_pos hNreal D) htest'
  rw [Real.log_pow, Real.log_rpow (by linarith)] at hlog'
  change (D : ℝ) - (D : ℝ) * _ / _ ≤ _
  rw [sub_le_iff_le_add', ← sub_le_iff_le_add, le_div_iff₀ (Real.log_pos hnreal)]
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ (D : ℝ) by positivity)]

open Filter
open scoped Topology

/-- The qualitative limit asserted in the opening step of the proof of
Theorem 1.5(b), for all d and all positive p=k+1. -/
theorem criticalT_tendsto_add (d k : ℕ) :
    Tendsto (criticalT d (k + 1)) atTop (𝓝 ((d + (k + 1) : ℕ) : ℝ)) := by
  let D : ℝ := (d + (k + 1) : ℕ)
  let C := D * Real.log (2 * ((d : ℝ) + 1))
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ => D - C / Real.log n) atTop (𝓝 D) := by
    simpa using (tendsto_const_nhds (x := D)).sub ((tendsto_const_nhds (x := C)).div_atTop hlog)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (2 * (d + 1))] with n hn
    exact largeSide_coarse_lower d k n hn
  · exact Eventually.of_forall (criticalT_le_add d k)


/-- Recover x₁ coordinatewise from x₂, x₁+h₁ and x₁+h₂ by their binary majority. -/
private theorem binary_majority {m : ℕ} {A : Finset (Lattice m)} (hA : A ⊆ box m 2)
    {x y : Lattice m} {h : Fin 2 → Lattice m}
    (hx : ∀ s : Finset (Fin 2), x + ∑ i ∈ s, h i ∈ A)
    (hy : ∀ s : Finset (Fin 2), y + ∑ i ∈ s, h i ∈ A) (j : Fin m) :
    x j = if 2 ≤ y j + (x + h 0) j + (x + h 1) j then 1 else 0 := by
  have bounds (w : Lattice m) (hw : w ∈ A) : 0 ≤ w j ∧ w j < 2 :=
    Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (hA hw) j)
  have X := bounds _ (hx ∅)
  have Y := bounds _ (hy ∅)
  have U := bounds _ (hx {0})
  have V := bounds _ (hx {1})
  have W := bounds _ (hx {0,1})
  have U' := bounds _ (hy {0})
  have V' := bounds _ (hy {1})
  simp at X Y U V W U' V'
  simp only [Pi.add_apply]
  by_cases hY : y j = 0 <;> split <;> omega

/-- Special case of Theorem 1.5(a). On a binary cube, the energy with d=p=2
is bounded by |A|³. Project a configuration to three of its vertices. The
missing first base is their coordinatewise majority, so the projection is injective. -/
theorem binary_energy_two_two_le {m : ℕ} (A : Finset (Lattice m)) (hA : A ⊆ box m 2) :
    energy 2 2 A ≤ A.card ^ 3 := by
  classical
  let H := Fintype.piFinset (fun _ : Fin 2 => A - A)
  let P (h : Fin 2 → Lattice m) := A.filter fun x => ∀ s : Finset (Fin 2), x + ∑ i ∈ s, h i ∈ A
  let S := H.sigma fun h => P h ×ˢ P h
  let T := A ×ˢ (A ×ˢ A)
  let F (w : Σ _ : Fin 2 → Lattice m, Lattice m × Lattice m) : Lattice m × Lattice m × Lattice m :=
    (w.2.2, w.2.1 + w.1 0, w.2.1 + w.1 1)
  have hS : S.card = energy 2 2 A := by
    simp [S, H, P, energy, baseCount, pow_two]
  have hT : T.card = A.card ^ 3 := by simp [T, pow_succ, Nat.mul_assoc]
  rw [← hS, ← hT]
  apply Finset.card_le_card_of_injOn F
  · rintro ⟨h, x, y⟩ hw
    obtain ⟨_, hp⟩ := Finset.mem_sigma.mp hw
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, _⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_product.mpr ⟨hy, Finset.mem_product.mpr ⟨by simpa using hx {0}, by simpa using hx {1}⟩⟩
  · rintro ⟨h, x, y⟩ hw ⟨l, z, t⟩ hw' heq
    obtain ⟨_, hp⟩ := Finset.mem_sigma.mp hw
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, hy⟩ := Finset.mem_filter.mp hy
    obtain ⟨_, hp'⟩ := Finset.mem_sigma.mp hw'
    obtain ⟨hz, ht⟩ := Finset.mem_product.mp hp'
    obtain ⟨_, hz⟩ := Finset.mem_filter.mp hz
    obtain ⟨_, ht⟩ := Finset.mem_filter.mp ht
    change (y, x + h 0, x + h 1) = (t, z + l 0, z + l 1) at heq
    obtain ⟨rfl, he₀, he₁⟩ := (Prod.mk.injEq ..).mp heq |>.imp_right (Prod.mk.injEq ..).mp
    have hxz : x = z := by
      ext j
      rw [binary_majority (x := x) (y := y) (h := h) hA hx hy j,
        binary_majority (x := z) (y := y) (h := l) hA hz ht j, he₀, he₁]
    subst z
    have hhl : h = l := by
      funext i
      fin_cases i
      · exact add_left_cancel he₀
      · exact add_left_cancel he₁
    subst l
    rfl

/-- Exact set exponent t₂,₂,₂ = 3, simultaneously over every ambient dimension. -/
theorem binary_criticalT_two_two : criticalT 2 2 2 = 3 := by
  apply le_antisymm
  · apply csInf_le (show BddBelow (setExponents 2 2 2) from ⟨0, fun t ht => ht.1.le⟩)
    refine ⟨by norm_num, ?_⟩
    intro m A hA
    norm_cast
    exact binary_energy_two_two_le A hA
  · have h := binary_criticalT_lower 2 1
    have hlog : logTwo 8 = 3 := by
      apply (Real.logb_eq_iff_rpow_eq (by norm_num : 0 < (2:ℝ)) (by norm_num : (2:ℝ) ≠ 1)
        (by norm_num)).2
      norm_num
    norm_num only [Nat.cast_ofNat] at h
    exact hlog ▸ h

/-- Increasing the side length increases the family of test sets. -/
theorem box_mono {m a b : ℕ} (hab : a ≤ b) : box m a ⊆ box m b := by
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro i
  obtain ⟨h₀,h₁⟩ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx i)
  exact Finset.mem_Ico.mpr ⟨h₀, h₁.trans_le (by exact_mod_cast hab)⟩

theorem criticalT_mono_side (d k : ℕ) {a b : ℕ} (hab : a ≤ b) :
    criticalT d (k + 1) a ≤ criticalT d (k + 1) b := by
  apply le_csInf ⟨_, add_mem_setExponents d k b⟩
  intro t ht
  apply csInf_le (show BddBelow (setExponents d (k + 1) a) from ⟨0, fun s hs => hs.1.le⟩)
  exact ⟨ht.1, fun m A hA => ht.2 m A (hA.trans (box_mono hab))⟩

/-- The minimizing set exponent is attained, as asserted in Proposition 8.1.
For sets of size at least two, take logarithms before taking the infimum. -/
theorem criticalT_isLeast (d k n : ℕ) (hn : 2 ≤ n) :
    IsLeast (setExponents d (k + 1) n) (criticalT d (k + 1) n) := by
  have hpos : 0 < criticalT d (k + 1) n := by
    have h2 : 1 < (2 : ℝ) ^ (k + 1) + 2 * d := by
      have hpow : 1 ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith [show 0 ≤ (d : ℝ) by positivity]
    exact (Real.logb_pos (by norm_num) h2).trans_le
      ((binary_criticalT_lower d k).trans (criticalT_mono_side d k hn))
  refine ⟨⟨hpos, ?_⟩, fun t ht => csInf_le ⟨0, fun s hs => hs.1.le⟩ ht⟩
  intro m A hA
  have hcoarse := (add_mem_setExponents d k n).2 m A hA
  rcases lt_trichotomy A.card 1 with hsmall | hone | hlarge
  · have hzero : A.card = 0 := by omega
    rw [hzero, Nat.cast_zero, Real.zero_rpow (by positivity)] at hcoarse
    simpa [hzero, Real.zero_rpow hpos.ne'] using hcoarse
  · simpa [hone] using hcoarse
  · by_cases he : energy d (k + 1) A = 0
    · simp [he, Real.rpow_nonneg]
    have hp : 0 < (energy d (k + 1) A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he
    have hbase : 1 < (A.card : ℝ) := by exact_mod_cast hlarge
    apply (Real.logb_le_iff_le_rpow hbase hp).mp
    apply le_csInf ⟨_, add_mem_setExponents d k n⟩
    intro t ht
    exact (Real.logb_le_iff_le_rpow hbase hp).mpr (ht.2 m A hA)

/-- Cartesian products factor the number of admissible bases coordinate by coordinate. -/
theorem baseCount_piFinset {m d : ℕ} (A : Fin m → Finset G) (h : Fin d → Fin m → G) :
    baseCount (Fintype.piFinset A) h = ∏ j, baseCount (A j) (fun i => h i j) := by
  classical
  unfold baseCount
  rw [← Fintype.card_piFinset]
  congr 1
  ext x
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Pi.add_apply, Finset.sum_apply]
  aesop

/-- Exact tensorization for the energies of Cartesian products (the sharpness test in §8). -/
theorem energy_piFinset {m : ℕ} (d p : ℕ) (A : Fin m → Finset G) :
    energy d p (Fintype.piFinset A) = ∏ j, energy d p (A j) := by
  classical
  unfold energy
  rw [← Fintype.piFinset_sub, Finset.prod_univ_sum]
  refine Finset.sum_bij' (fun h _ j i => h i j) (fun h _ i j => h j i) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Fintype.mem_piFinset] at hh ⊢
    exact fun j i => hh i j
  · intro h hh
    simp only [Fintype.mem_piFinset] at hh ⊢
    exact fun i j => hh j i
  · intro _ _; rfl
  · intro _ _; rfl
  · intro h _
    rw [baseCount_piFinset, Finset.prod_pow]

/-- The equality witness on the full binary cube, in all dimensions m and for every
degree d and positive integer p=k+1. -/
theorem full_binary_box_energy (m d k : ℕ) :
    energy d (k + 1) (box m 2) = (2 ^ (k + 1) + 2 * d) ^ m := by
  have hbox : box 1 2 = binaryPair := by
    apply Finset.Subset.antisymm _ binaryPair_subset
    intro x hx
    have := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx (0 : Fin 1))
    apply binaryPair_mem.mpr
    omega
  have hsingle : energy d (k + 1) (Finset.Ico (0 : ℤ) 2) = 2 ^ (k + 1) + 2 * d := by
    have h := energy_piFinset d (k + 1) (fun _ : Fin 1 => Finset.Ico (0 : ℤ) 2)
    change energy _ _ (box 1 2) = _ at h
    rw [hbox] at h
    unfold binaryPair at h
    rw [binary_energy] at h
    simpa using h.symm
  simpa [hsingle, box] using energy_piFinset d (k + 1) (fun _ : Fin m => Finset.Ico (0 : ℤ) 2)

private def Sparse (a : Fin d → ℤ) : Prop :=
  a = 0 ∨ ∃ (i : Fin d) (v : ℤ), v ≠ 0 ∧ a = fun j => if j = i then v else 0

private theorem sparse_coord {d m : ℕ} {x : Lattice m} {h : Fin d → Lattice m}
    (hc : ∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ box m 2) (j : Fin m) :
    Sparse (fun i => h i j) := by
  let a : Fin d → Lattice 1 := fun i _ => h i j
  let b : Lattice 1 := fun _ => x j
  have hb (s : Finset (Fin d)) : b + ∑ i ∈ s, a i ∈ binaryPair := by
    apply binaryPair_mem.mpr
    have hbit := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (hc s) j)
    simp [b, a, Finset.sum_apply] at hbit ⊢
    omega
  have hp : 0 < baseCount binaryPair a := by
    apply Finset.card_pos.mpr
    exact ⟨b, Finset.mem_filter.mpr ⟨by simpa using hb ∅, hb⟩⟩
  by_cases hz : a = 0
  · exact Or.inl (funext (fun i => congrFun (congrFun hz i) 0))
  obtain ⟨⟨i,B⟩, hh⟩ := increments_of_pos hp hz
  right
  refine ⟨i, if B then 1 else -1, by cases B <;> decide, ?_⟩
  funext z
  have he := congrFun (congrFun hh z) (0 : Fin 1)
  by_cases hi : z = i <;> cases B <;> simpa [a, signedStep, hi] using he

private def probeSet {r d : ℕ} (code : Fin d ↪ (Fin r → Bool)) (j : Fin r) : Finset (Fin d) :=
  Finset.univ.filter fun i => code i j = true

private def probes {r d : ℕ} (code : Fin d ↪ (Fin r → Bool)) (a : Fin d → ℤ) :
    ℤ × (Fin r → ℤ) :=
  (∑ i, a i, fun j => ∑ i ∈ probeSet code j, a i)

/-- The total increment and the sums over the binary digits of its direction
recover any tuple with at most one nonzero coordinate. -/
private theorem sparse_injective {d r : ℕ} (code : Fin d ↪ (Fin r → Bool))
    {a b : Fin d → ℤ} (ha : Sparse a) (hb : Sparse b) (heq : probes code a = probes code b) :
    a = b := by
  have htot := congrArg Prod.fst heq
  rcases ha with rfl | ⟨i, v, hv, rfl⟩ <;> rcases hb with rfl | ⟨l, w, hw, rfl⟩
  · rfl
  · simp [probes] at htot
    exact False.elim (hw htot.symm)
  · simp [probes] at htot
    exact False.elim (hv htot)
  · simp [probes] at htot
    subst w
    have hbits : code i = code l := by
      funext j
      have hprobe := congrFun (congrArg Prod.snd heq) j
      cases hi : code i j <;> cases hl : code l j <;> first | rfl | simp [probes, probeSet, hi, hl, hv, Ne.symm hv] at hprobe
    rw [code.injective hbits]

/-- Test a binary configuration at its p bases, at the opposite vertex of the
first cube, and at r coded vertices of that cube. These p+1+r vertices recover
the configuration whenever the d directions admit distinct r-bit labels. -/
theorem binary_energy_le_coded {d r : ℕ} (code : Fin d ↪ (Fin r → Bool)) (k m : ℕ)
    (A : Finset (Lattice m)) (hA : A ⊆ box m 2) :
    energy d (k + 1) A ≤ A.card ^ ((k + 1) + (1 + r)) := by
  classical
  let H := Fintype.piFinset (fun _ : Fin d => A - A)
  let P (h : Fin d → Lattice m) := A.filter fun x => ∀ s : Finset (Fin d), x + ∑ i ∈ s, h i ∈ A
  let S := H.sigma fun h => Fintype.piFinset (fun _ : Fin (k + 1) => P h)
  let T := Fintype.piFinset (fun _ : Fin (k + 1) => A) ×ˢ (A ×ˢ Fintype.piFinset (fun _ : Fin r => A))
  let F (w : Σ _ : Fin d → Lattice m, Fin (k + 1) → Lattice m) :=
    (w.2, w.2 0 + ∑ i, w.1 i, fun j => w.2 0 + ∑ i ∈ probeSet code j, w.1 i)
  have hs : S.card = energy d (k + 1) A := by simp [S, H, P, energy, baseCount]
  have ht : T.card = A.card ^ ((k + 1) + (1 + r)) := by simp [T, pow_add]
  rw [← hs, ← ht]
  apply Finset.card_le_card_of_injOn F
  · rintro ⟨h, x⟩ hw
    have hx : ∀ t, x t ∈ P h := Fintype.mem_piFinset.mp (Finset.mem_sigma.mp hw).2
    have hx0 := (Finset.mem_filter.mp (hx 0)).2
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun t => (Finset.mem_filter.mp (hx t)).1),
      Finset.mem_product.mpr ⟨hx0 _, Fintype.mem_piFinset.mpr (fun _ => hx0 _)⟩⟩
  · rintro ⟨h, x⟩ hw ⟨l, z⟩ hw' heq
    have hx : ∀ t, x t ∈ P h := Fintype.mem_piFinset.mp (Finset.mem_sigma.mp hw).2
    have hz : ∀ t, z t ∈ P l := Fintype.mem_piFinset.mp (Finset.mem_sigma.mp hw').2
    have hxz : x = z := congrArg Prod.fst heq
    subst z
    have hh := congrArg (fun t => t.2.1) heq
    have hj := congrArg (fun t => t.2.2) heq
    change x 0 + ∑ i, h i = x 0 + ∑ i, l i at hh
    have hsums := add_left_cancel hh
    have hhl : h = l := by
      funext i j
      have ha := sparse_coord (fun s => hA ((Finset.mem_filter.mp (hx 0)).2 s)) j
      have hb := sparse_coord (fun s => hA ((Finset.mem_filter.mp (hz 0)).2 s)) j
      apply congrFun (sparse_injective code ha hb ?_) i
      apply Prod.ext
      · simpa [probes, Finset.sum_apply] using congrFun hsums j
      · funext s
        have HP := congrFun hj s
        change x 0 + _ = x 0 + _ at HP
        simpa [probes, Finset.sum_apply] using congrFun (add_left_cancel HP) j
    subst l; rfl

/-- A binary-cube upper bound growing only logarithmically with d. -/
theorem binary_criticalT_le_log (d k : ℕ) :
    criticalT d (k + 1) 2 ≤ (k + 1 : ℕ) + (1 + (Nat.clog 2 d : ℝ)) := by
  let r := Nat.clog 2 d
  have hcard : d ≤ Fintype.card (Fin r → Bool) := by
    simpa [r] using (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_refl (Nat.clog 2 d))
  let code := (Fin.castLEEmb hcard).trans (Fintype.equivFin (Fin r → Bool)).symm.toEmbedding
  apply csInf_le (show BddBelow (setExponents d (k + 1) 2) from ⟨0, fun s hs => hs.1.le⟩)
  refine ⟨by positivity, ?_⟩
  intro m A hA
  have hle := binary_energy_le_coded code k m A hA
  convert (show ((energy d (k + 1) A : ℕ) : ℝ) ≤
      (A.card : ℝ) ^ (((k + 1) + (1 + r) : ℕ) : ℝ) from by
    rw [Real.rpow_natCast]; exact_mod_cast hle) using 2; push_cast; rfl

/-- The leading logarithmic term in the case n=2 of the large-degree regime.
Theorem 1.5(c) further identifies an additive error tending to zero. -/
theorem binary_criticalT_log_ratio (k : ℕ) :
    Tendsto (fun d : ℕ => criticalT d (k + 1) 2 / logTwo (2 * (d : ℝ))) atTop (𝓝 1) := by
  let L := fun d : ℕ => logTwo (2 * (d : ℝ))
  have hlim : Tendsto L atTop atTop := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop)
  have hbig : Tendsto (fun d => 1 + ((k : ℝ) + 3) / L d) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add
      ((tendsto_const_nhds (x := (k:ℝ) + 3)).div_atTop hlim)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbig
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hL : 0 < L d := Real.logb_pos (by norm_num) (by linarith)
    apply (le_div_iff₀ hL).mpr
    rw [one_mul]
    apply le_trans ?_ (binary_criticalT_lower d k)
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith [show 0 < (2 : ℝ) ^ (k + 1) by positivity])
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hL : 0 < L d := Real.logb_pos (by norm_num) (by linarith)
    have hceil : Nat.clog 2 d ≤ Nat.log 2 d + 1 :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_pow_succ_log_self (by decide) d).le
    have hceil' : (Nat.clog 2 d : ℝ) ≤ (Nat.log 2 d : ℝ) + 1 := by exact_mod_cast hceil
    have hlog : Real.logb 2 d ≤ L d :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    change _ / L d ≤ _
    apply (div_le_iff₀ hL).mpr
    rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul]
    have ht := binary_criticalT_le_log d k
    push_cast at ht
    have hfloor : (Nat.log 2 d : ℝ) ≤ Real.logb 2 d := by simpa using Real.natLog_le_logb d 2
    linarith


/-- Sum over admissible increments in a binary interval. The zero tuple and
the signed single-direction tuples exhaust all configurations with a base point. -/
theorem sum_binary_steps {M : Type*} [AddCommMonoid M] (d : ℕ) (F : (Fin d → Lattice 1) → M)
    (hF : ∀ h, baseCount ({0,1} : Finset (Lattice 1)) h = 0 → F h = 0) :
    ∑ h ∈ Fintype.piFinset (fun _ : Fin d => ({0,1} : Finset (Lattice 1)) - {0,1}), F h =
      F 0 + ∑ u : Fin d × Bool, F (fun j => if j = u.1 then (if u.2 then 1 else -1) else 0) := by
  let B := Finset.univ.image (signedStep (d := d))
  have hz : (0 : Fin d → Lattice 1) ∉ B := by
    rintro hh
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hh
    exact signedStep_ne_zero u hu
  have hsub : insert (0 : Fin d → Lattice 1) B ⊆
      Fintype.piFinset (fun _ : Fin d => binaryPair-binaryPair) := by
    intro h hh
    by_contra hn
    have hx := baseCount_eq_zero_outside binaryPair h hn
    rcases Finset.mem_insert.mp hh with rfl | hh
    · simp [baseCount_zero, card_binaryPair] at hx
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hh
      exact (baseCount_signedStep_pos u).ne' hx
  change (∑ h ∈ Fintype.piFinset (fun _ : Fin d => binaryPair-binaryPair), F h) = F 0 + ∑ u, F (signedStep u)
  rw [← Finset.sum_subset hsub, Finset.sum_insert hz]
  · dsimp [B]
    rw [Finset.sum_image (signedStep_injective d).injOn]
  intro h _ hh
  apply hF
  by_contra hn
  obtain ⟨u, rfl⟩ := increments_of_pos (Nat.pos_of_ne_zero hn) (fun he => hh (he ▸ Finset.mem_insert_self _ _))
  exact hh (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩))

end LpGowers.Discrete
