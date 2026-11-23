module

public import LpGowers.DiscreteFunctional
public import Mathlib.Analysis.MeanInequalities

/-! # The exact binary functional exponent at d=p=2 -/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise NNReal ENNReal

namespace LpGowers.Discrete

private abbrev Config (m : ℕ) := (Fin 2 → Lattice m) × (Lattice m × Lattice m)

private def validBases {m : ℕ} (A : Finset (Lattice m)) (h : Fin 2 → Lattice m) :=
  A.filter (fits A h)

private def configs {m : ℕ} (A : Finset (Lattice m)) : Finset (Config m) :=
  (Fintype.piFinset (fun _ : Fin 2 => A - A) ×ˢ (A ×ˢ A)).filter
    fun c => fits A c.1 c.2.1 ∧ fits A c.1 c.2.2

private def face {m : ℕ} (f : Lattice m → ℝ≥0) (h : Fin 2 → Lattice m) (x : Lattice m) : ℝ≥0 :=
  f x * f (x + h 1) * (f (x + h 0) * f (x + h 0 + h 1))

private theorem face_vanish {m : ℕ} (A : Finset (Lattice m)) (f : Lattice m → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) (h : Fin 2 → Lattice m) {x : Lattice m} (hx : x ∉ validBases A h) :
    face f h x = 0 := by
  by_contra hn
  have hkeep (z : Lattice m) (hz : f z ≠ 0) : z ∈ A := by by_contra zA; exact hz (hf z zA)
  simp only [face, mul_ne_zero_iff] at hn
  obtain ⟨⟨h₁,h₂⟩, h₃,h₄⟩ := hn
  apply hx
  refine Finset.mem_filter.mpr ⟨hkeep _ h₁, ?_⟩
  intro s
  have hs : s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {0,1} := by
    clear * - s
    decide +revert
  rcases hs with rfl | rfl | rfl | rfl
  · simpa using hkeep _ h₁
  · simpa using hkeep _ h₃
  · simpa using hkeep _ h₂
  · simpa [add_assoc] using hkeep _ h₄

private theorem correlation_face {m : ℕ} (A : Finset (Lattice m)) (f : Lattice m → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) (h : Fin 2 → Lattice m) :
    autocorrelation Measure.count 2 f h = ((∑ x ∈ validBases A h, face f h x : ℝ≥0) : ℝ≥0∞) := by
  rw [autocorrelation, lintegral_count, tsum_eq_sum (s := validBases A h)]
  · simp [cubeProduct, face, Fin.tail]
  · intro x hx
    have hzero := face_vanish A f hf h hx
    simpa [cubeProduct, face, Fin.tail] using congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) hzero

private theorem gowers_count_config {m : ℕ} (A : Finset (Lattice m)) (f : Lattice m → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) :
    gowers Measure.count 2 2 f =
      ((∑ c ∈ configs A, face f c.1 c.2.1 * face f c.1 c.2.2 : ℝ≥0) : ℝ≥0∞) ^ (1/8 : ℝ) := by
  let H := Fintype.piFinset (fun _ : Fin 2 => A - A)
  have he : ∫⁻ h : Fin 2 → Lattice m, autocorrelation Measure.count 2 f h ^ (2 : ℕ) ∂Measure.count =
      ((∑ c ∈ configs A, face f c.1 c.2.1 * face f c.1 c.2.2 : ℝ≥0) : ℝ≥0∞) := by
    have decomp : (∑ h ∈ H, (∑ x ∈ validBases A h, face f h x)^2) =
        ∑ c ∈ configs A, face f c.1 c.2.1 * face f c.1 c.2.2 := by
      simp only [configs, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      rw [pow_two, Finset.sum_mul_sum]
      simp only [validBases, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : fits A h x
      · simp [hx]
      · simp [hx]
    rw [lintegral_count, tsum_eq_sum (s := H), ← decomp]
    · simp [correlation_face A f hf]
    · intro h hn
      have hzero := baseCount_eq_zero_outside A h hn
      have hv : validBases A h = ∅ := Finset.card_eq_zero.mp hzero
      simp [correlation_face A f hf, hv]
  unfold gowers lp
  rw [cubeMeasure_count]
  norm_num only [ENNReal.rpow_ofNat]
  rw [he, ← ENNReal.rpow_mul]
  norm_num
private abbrev Vertex := Bool × Bool × Bool

private def neighbor (i : Fin 3) (v : Vertex) : Vertex :=
  if i = 0 then (!v.1,v.2.1,v.2.2) else if i = 1 then (v.1,!v.2.1,v.2.2) else (v.1,v.2.1,!v.2.2)

private def flipNeighbor (i : Fin 3) : Equiv.Perm Vertex :=
  (show Function.Involutive (neighbor i) by
    rintro ⟨a, b, c⟩; fin_cases i <;> simp [neighbor]).toPerm _

private def vertex {m : ℕ} (c : Config m) (v : Vertex) : Lattice m :=
  (if v.1 then c.2.2 else c.2.1) + (if v.2.1 then c.1 0 else 0) + (if v.2.2 then c.1 1 else 0)

private theorem vertex_mem {m : ℕ} {B : Finset (Lattice m)} (c : Config m) (hc : c ∈ configs B)
    (v : Vertex) : vertex c v ∈ B := by
  rcases v with ⟨j, a, b⟩
  obtain ⟨hx,hy⟩ := (Finset.mem_filter.mp hc).2
  cases j <;> cases a <;> cases b <;>
    first | simpa [vertex] using hx ∅ | simpa [vertex] using hx {0} |
      simpa [vertex] using hx {1} | simpa [vertex, add_assoc] using hx {0,1} |
      simpa [vertex] using hy ∅ | simpa [vertex] using hy {0} |
      simpa [vertex] using hy {1} | simpa [vertex, add_assoc] using hy {0,1}

private theorem vertex_rule {m : ℕ} (c : Config m) (hc : c ∈ configs (box m 2))
    (v : Vertex) (j : Fin m) :
    vertex c v j =
      if 2 ≤ vertex c (neighbor 0 v) j + vertex c (neighbor 1 v) j + vertex c (neighbor 2 v) j
        then 1 else 0 := by
  have bound (w : Vertex) : 0 ≤ vertex c w j ∧ vertex c w j < 2 :=
    Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (vertex_mem c hc w) j)
  have h000 := bound (false,false,false)
  have h001 := bound (false,false,true)
  have h010 := bound (false,true,false)
  have h011 := bound (false,true,true)
  have h100 := bound (true,false,false)
  have h101 := bound (true,false,true)
  have h110 := bound (true,true,false)
  have h111 := bound (true,true,true)
  simp [vertex] at h000 h001 h010 h011 h100 h101 h110 h111
  rcases v with ⟨a,b,e⟩
  cases a <;> cases b <;> cases e <;> simp [vertex,neighbor] <;> split <;> omega

/-- Each oriented triple of neighboring vertices determines a valid binary
configuration. The central vertex is their coordinatewise binary majority. -/
private theorem neighbors_injOn {m : ℕ} (v : Vertex) :
    Set.InjOn (fun c : Config m => fun i : Fin 3 => vertex c (neighbor i v))
      (configs (box m 2) : Set (Config m)) := by
  rintro ⟨h,x,y⟩ hc ⟨l,z,t⟩ he heq
  have hc0 : vertex (h,x,y) v = vertex (l,z,t) v := by
    funext j
    rw [vertex_rule _ hc v j, vertex_rule _ he v j]
    rw [show vertex (h,x,y) (neighbor 0 v) = vertex (l,z,t) (neighbor 0 v) from congrFun heq 0,
      show vertex (h,x,y) (neighbor 1 v) = vertex (l,z,t) (neighbor 1 v) from congrFun heq 1,
      show vertex (h,x,y) (neighbor 2 v) = vertex (l,z,t) (neighbor 2 v) from congrFun heq 2]
  have Hj (j : Fin m) : x j = z j ∧ y j = t j ∧ h 0 j = l 0 j ∧ h 1 j = l 1 j := by
    have hx := congrFun hc0 j
    have h0 := congrFun (congrFun heq 0) j
    have h1 := congrFun (congrFun heq 1) j
    have h2 := congrFun (congrFun heq 2) j
    rcases v with ⟨b₀,b₁,b₂⟩
    cases b₀ <;> cases b₁ <;> cases b₂ <;> simp [vertex, neighbor] at hx h0 h1 h2 <;> omega
  have hhl : h = l := by
    funext i j
    fin_cases i
    · exact (Hj j).2.2.1
    · exact (Hj j).2.2.2
  exact Prod.ext hhl (Prod.ext (funext (fun j => (Hj j).1)) (funext (fun j => (Hj j).2.1)))

private theorem face_prod {m : ℕ} (f : Lattice m → ℝ≥0) (c : Config m) :
    face f c.1 c.2.1 * face f c.1 c.2.2 = ∏ v : Vertex, f (vertex c v) := by
  simp [Fintype.prod_prod_type, vertex, face]
  ring

private def tripleWeight {m : ℕ} (f : Lattice m → ℝ≥0) (w : Fin 3 → Lattice m) : ℝ≥0 :=
  ∏ i, f (w i) ^ (8/3 : ℝ)

/-- The AM–GM argument over all eight choices of the central vertex. -/
private theorem average_triples {m : ℕ} (f : Lattice m → ℝ≥0) (c : Config m) :
    (∏ v : Vertex, f (vertex c v)) ≤ ∑ v : Vertex, (1/8 : ℝ≥0) *
      tripleWeight f (fun i => vertex c (neighbor i v)) := by
  let g := fun v => f (vertex c v)
  have hweight : (∑ _ : Vertex, (1/8 : ℝ≥0)) = 1 := by norm_num [Fintype.card_prod]
  have h := NNReal.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Vertex => 1/8)
    (fun v => tripleWeight f (fun i => vertex c (neighbor i v))) hweight
  refine le_trans (le_of_eq ?_) h
  change (∏ v, g v) = ∏ v : Vertex, (∏ i : Fin 3, g (neighbor i v) ^ (8/3 : ℝ)) ^ (((1/8 : ℝ≥0):ℝ))
  push_cast
  simp_rw [NNReal.finsetProd_rpow, ← NNReal.rpow_mul]
  rw [Finset.prod_comm]
  have hprod (i : Fin 3) : (∏ v, g (neighbor i v)) = ∏ v, g v :=
    Equiv.prod_comp (flipNeighbor i) g
  simp_rw [hprod]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  norm_num

private theorem sum_triple_le (m : ℕ) (f : Lattice m → ℝ≥0) (v : Vertex) :
    ∑ c ∈ configs (box m 2), tripleWeight f (fun i => vertex c (neighbor i v)) ≤
      (∑ x ∈ box m 2, f x ^ (8/3 : ℝ)) ^ (3 : ℕ) := by
  let B := box m 2
  let F := fun c : Config m => fun i : Fin 3 => vertex c (neighbor i v)
  have hsub : (configs B).image F ⊆ Fintype.piFinset (fun _ : Fin 3 => B) := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
    exact Fintype.mem_piFinset.mpr (fun _ => vertex_mem c hc _)
  calc
    _ = ∑ w ∈ (configs B).image F, tripleWeight f w := (Finset.sum_image (neighbors_injOn v)).symm
    _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin 3 => B), tripleWeight f w :=
      Finset.sum_le_sum_of_subset hsub
    _ = _ := (Finset.sum_pow' B (fun x => f x ^ (8/3 : ℝ)) 3).symm

/-- Binary cubes with d=p=2 satisfy the sharp functional estimate at q=8/3
in every dimension. Each vertex occurs in three of the eight neighbor triples. -/
theorem binary_eight_thirds_admissible : (8/3 : ℝ) ∈ functionExponents 2 2 2 := by
  refine ⟨by norm_num, ?_⟩
  intro m f hf
  let B := box m 2
  let S := configs B
  let W := ∑ x ∈ B, f x ^ (8/3 : ℝ)
  have hm : ∑ c ∈ S, face f c.1 c.2.1 * face f c.1 c.2.2 ≤ W ^ (3 : ℕ) := calc
    _ ≤ ∑ c ∈ S, ∑ v : Vertex, (1/8 : ℝ≥0) *
          tripleWeight f (fun i => vertex c (neighbor i v)) :=
      Finset.sum_le_sum fun c _ => (face_prod f c).le.trans (average_triples f c)
    _ = ∑ v : Vertex, (1/8 : ℝ≥0) * ∑ c ∈ S, tripleWeight f (fun i => vertex c (neighbor i v)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _ : Vertex, (1/8 : ℝ≥0) * W ^ (3 : ℕ) := by
      exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (sum_triple_le m f v) (by positivity))
    _ = _ := by norm_num [Fintype.card_prod, ← mul_assoc]
  norm_num only [Nat.cast_ofNat]
  rw [gowers_count_config B f hf, lp_count_finite B f hf (by norm_num)]
  refine (ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr hm) (by norm_num : (0:ℝ) ≤ 1/8)).trans_eq ?_
  rw [← ENNReal.coe_rpow_of_nonneg _ (by norm_num), ← NNReal.rpow_natCast _ 3, ← NNReal.rpow_mul]
  norm_num [W]

/-- Both exact exponents from Theorem 1.5(a) for d=p=2, uniformly over m. -/
theorem binary_critical_two_two :
    criticalT 2 2 2 = 3 ∧ criticalQ 2 2 2 = 8/3 :=
  ⟨binary_criticalT_two_two, le_antisymm binary_criticalQ_two_two_le
    ((criticalQ_isGreatest 2 1 2 (by decide)).2 binary_eight_thirds_admissible)⟩

/-- By the marginal identity, the same sharp exponents hold for ordinary
three-dimensional Gowers cubes (d=3,p=1). -/
theorem binary_critical_three_one :
    criticalT 3 1 2 = 3 ∧ criticalQ 3 1 2 = 8/3 := by
  have h := critical_succ_one 2 2
  exact ⟨h.1.trans binary_critical_two_two.1, h.2.trans binary_critical_two_two.2⟩

end LpGowers.Discrete
