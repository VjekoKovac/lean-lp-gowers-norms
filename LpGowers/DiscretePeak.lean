module

public import LpGowers.DiscreteMixed
import Mathlib.Tactic

/-! A point-mass expansion for discrete additive energy. The four linear
terms vanish because any three coincident vertices of a parallelogram
determine the fourth. The eleven higher-order terms are controlled by
the mixed Gowers–Cauchy–Schwarz inequality. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace LpGowers.Discrete

private abbrev Vertex := Finset (Fin 2)

private theorem fourth_vertex {m : ℕ} (v : Vertex) (x x₀ : Lattice m) (h : Fin 2 → Lattice m)
    (H : ∀ s : Vertex, s ≠ v → x + ∑ i ∈ s, h i = x₀) : x + ∑ i ∈ v, h i = x₀ := by
  have hcases : v = ∅ ∨ v = {0} ∨ v = {1} ∨ v = {0,1} := by
    exact (by decide : ∀ w : Vertex, w = ∅ ∨ w = {0} ∨ w = {1} ∨ w = {0,1}) v
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    have ha := H ∅
    have hb := H {0}
    have hc := H {1}
    have hd := H {0,1}
    simp only [Finset.sum_empty, add_zero, Finset.sum_singleton, Finset.sum_pair (by decide : (0:Fin 2) ≠ 1)] at ha hb hc hd ⊢
    funext z
    try have a := congrFun (ha (by decide)) z
    try have b := congrFun (hb (by decide)) z
    try have c := congrFun (hc (by decide)) z
    try have e := congrFun (hd (by decide)) z
    simp only [Pi.add_apply] at *
    omega

private def maskProduct {m : ℕ} (U V : Lattice m → ℝ≥0) (s : Finset Vertex)
    (h : Fin 2 → Lattice m) (x : Lattice m) : ℝ≥0∞ :=
  ∏ v : Vertex, ((if v ∈ s then V else U) (x + ∑ i ∈ v,h i) : ℝ≥0∞)

private theorem one_tail_vanishes {m : ℕ} (f : Lattice m → ℝ≥0) (x₀ : Lattice m)
    (v : Vertex) (h : Fin 2 → Lattice m) (x : Lattice m) :
    maskProduct (({x₀}:Set (Lattice m)).indicator f) (({x₀}ᶜ:Set (Lattice m)).indicator f) {v} h x = 0 := by
  classical
  by_cases H : ∀ s : Vertex, s ≠ v → x + ∑ i ∈ s,h i = x₀
  · apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [fourth_vertex v x x₀ h H]
  · push Not at H
    obtain ⟨s,hs,hhh⟩ := H
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [hs,hhh]

private theorem expand_peak {m : ℕ} (f U V : Lattice m → ℝ≥0) (hadd : ∀ x, f x = V x+U x)
    (h : Fin 2 → Lattice m) (x : Lattice m) :
    cubeProduct 2 f h x = ∑ s : Finset Vertex, maskProduct U V s h x := by
  rw [cubeProduct_vertices]
  simp_rw [hadd, ENNReal.coe_add]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  unfold maskProduct
  simp_rw [ite_apply, apply_ite]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [show (Finset.univ.filter (fun v : Vertex => v ∉ s)) = sᶜ by ext; simp]

/-- Raising the ordinary degree-two counting functional to its fourth power
makes the `11`-term quadratic tail estimate valid on every integer lattice. -/
theorem additive_energy_point_tail (m : ℕ) (f : Lattice m → ℝ≥0) (x₀ : Lattice m) :
    let a := (f x₀ : ℝ≥0∞)
    let T := lp Measure.count (4/3) (liftNN (({x₀}ᶜ : Set (Lattice m)).indicator f))
    (gowers Measure.count 2 1 f)^4 ≤ a^4 + 11*T^2*(max a T)^2 := by
  classical
  let U := ({x₀}:Set (Lattice m)).indicator f
  let V := ({x₀}ᶜ:Set (Lattice m)).indicator f
  let a := (f x₀:ℝ≥0∞)
  let T := lp Measure.count (4/3) (liftNN V)
  let M := max a T
  let E (s : Finset Vertex) := ∑' h : Fin 2 → Lattice m, ∑' x : Lattice m, maskProduct U V s h x
  have hsum : (gowers Measure.count 2 1 f)^4 = ∑ s, E s := by
    have h := gowers_count_nat_mass 2 0 f
    norm_num at h
    rw [h]
    have hs := expand_peak f U V (fun x => by by_cases hx:x=x₀ <;> simp [U,V,hx])
    simp_rw [hs,Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
    rfl
  have hA : gowers Measure.count 2 1 U ≤ a := by
    have hh := lebesgue_bound_degree_two (Measure.count : Measure (Lattice m)) (f:=U)
      (p:=1) (by norm_num) (measurable_of_countable _).aemeasurable
    norm_num [criticalExponent] at hh
    apply hh.trans_eq
    unfold lp
    rw [lintegral_count, tsum_eq_single x₀ (fun x hx => by simp [liftNN,U,hx])]
    simp only [liftNN,U,Set.indicator_of_mem (Set.mem_singleton x₀),← ENNReal.rpow_mul]
    norm_num [a]
  have hT : gowers Measure.count 2 1 V ≤ T := by
    simpa only [T, show criticalExponent 2 1 = 4/3 by norm_num [criticalExponent]] using
      lebesgue_bound_degree_two (Measure.count : Measure (Lattice m)) (f:=V) (p:=1)
        (by norm_num) (measurable_of_countable _).aemeasurable
  have hbound (s : Finset Vertex) : E s ≤ T^s.card * a^(4-s.card) := by
    have H := mixed_count_holder 2 0 (fun _ v => if v ∈ s then V else U)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.zero_add, pow_one, Nat.cast_one] at H
    apply H.trans
    have H' : (∏ v : Vertex, gowers Measure.count 2 1 (if v ∈ s then V else U)) ≤
        ∏ v : Vertex, if v ∈ s then T else a := by
      apply Finset.prod_le_prod
      intro v _
      split <;> simp_all
    apply H'.trans_eq
    rw [Finset.prod_ite]
    have hco : Finset.univ.filter (fun v : Vertex => v ∉ s) = sᶜ := by ext; simp
    simp [hco,Finset.card_compl,show Fintype.card Vertex=4 by decide]
  have hone s (hs : s.card=1) : E s = 0 := by
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simp only [E,U,V,one_tail_vanishes,tsum_zero]
  let C := T^2 * M^2
  let B := Finset.univ.filter (fun s : Finset Vertex => 2≤s.card)
  have hcard : B.card=11 := by decide
  have hrest (s : Finset Vertex) (hs : 2≤s.card) : E s ≤ C := by
    have hu : s.card≤4 := (Finset.card_le_univ s).trans_eq (by decide)
    obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le hs
    have hdeg : l + (4-s.card) = 2 := by omega
    apply (hbound s).trans
    calc
      _ = T^2 * (T^l * a^(4-s.card)) := by rw [hl,pow_add,mul_assoc]
      _ ≤ T^2 * (M^l * M^(4-s.card)) := by
        exact mul_le_mul_right (mul_le_mul' (pow_le_pow_left' (le_max_right a T) l)
          (pow_le_pow_left' (le_max_left a T) (4-s.card))) _
      _ = C := by rw [← pow_add,hdeg]
  rw [hsum]
  change _ ≤ a^4 + 11*T^2*M^2
  calc
    _ ≤ ∑ s : Finset Vertex, ((if s=∅ then a^4 else 0) + if 2≤s.card then C else 0) := by
      apply Finset.sum_le_sum
      intro s _
      rcases Nat.eq_zero_or_pos s.card with hz | hp
      · have h := Finset.card_eq_zero.mp hz
        simpa [h] using hbound s
      · by_cases hs : 2≤s.card
        · exact (hrest s hs).trans (by simp [hs])
        · rw [hone s (by omega)]
          exact zero_le
    _ = a^4 + 11*T^2*M^2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter (fun s : Finset Vertex => 2≤s.card)]
      have hsing : (∑ s : Finset Vertex, if s=∅ then a^4 else 0) = a^4 := by simp
      rw [hsing,Finset.sum_const,show (Finset.univ.filter (fun s : Finset Vertex => 2≤s.card)).card = 11 from hcard]
      simp [C,mul_assoc]

end LpGowers.Discrete
