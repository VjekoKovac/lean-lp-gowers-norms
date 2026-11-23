module

public import LpGowers.DiscreteEntropyUniform
public import LpGowers.DiscretePatternEnergy
public import LpGowers.DiscreteTensorization
import Mathlib.Tactic

/-! # From normalized pattern sums to the large-degree critical exponent -/

@[expose] public section
noncomputable section
open Filter MeasureTheory
open scoped Topology NNReal BigOperators Pointwise
namespace LpGowers.Discrete

private theorem finiteCubeProduct_scale {G : Type*} [AddCommGroup G] (d : ℕ) (c : ℝ≥0)
    (f : G→ℝ≥0) (h : Fin d→G) (x : G) :
    finiteCubeProduct d (fun y => c*f y) h x = c^(2^d)*finiteCubeProduct d f h x := by
  induction d generalizing x with
  | zero => simp [finiteCubeProduct]
  | succ d ih => simp only [finiteCubeProduct,ih,pow_succ (2:ℕ),mul_two,pow_add]; ring

private theorem weightedEnergy_scale {G : Type*} [AddCommGroup G] [DecidableEq G]
    (d p : ℕ) (A : Finset G) (c : ℝ≥0) (f : G→ℝ≥0) :
    weightedEnergy d p A (fun x => c*f x) = c^(2^d*p) * weightedEnergy d p A f := by
  simp only [weightedEnergy, finiteCubeProduct_scale, ← Finset.mul_sum, mul_pow, pow_mul]

private theorem box_sum_int (n : ℕ) (f : Lattice 1 → ℝ≥0) :
    ∑ x ∈ box 1 n, f x = ∑ j ∈ Finset.Ico 0 (n:ℤ), f (fun _ => j) := by
  apply Finset.sum_bij' (fun x _ => x 0) (fun j _ => (fun _ : Fin 1 => j)) ?_ ?_ ?_ ?_ ?_
  · exact fun x hx => Fintype.mem_piFinset.mp hx 0
  · exact fun j hj => Fintype.mem_piFinset.mpr fun _ => hj
  · intro x _; funext i; rw [Fin.eq_zero i]
  · intro _ _; rfl
  · intro x _; congr; funext i; rw [Fin.eq_zero i]

/-- If every normalized input passes the finite-pattern test at t, then t is
admissible in the original all-dimensional set inequality. -/
theorem setExponent_of_normalized_energy (N d k : ℕ) {t : ℝ} (ht : 0<t)
    (hbound : ∀ (g : ℤ→ℝ≥0),
      (∑ j ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g j) = 1 →
      (∀ j, j∉Finset.Ico 0 ((N+1:ℕ):ℤ) → g j=0) →
      weightedEnergy d (k+1) (box 1 (N+1)) (fun x => (g (x 0))^(t/((2:ℝ)^d*(k+1:ℕ)))) ≤ 1) :
    t ∈ setExponents d (k+1) (N+1) := by
  let V : ℝ := 2^d*(k+1:ℕ)
  let q := V/t
  have hV : 0<V := by dsimp [V]; positivity
  have hq : 0<q := div_pos hV ht
  have hqt : q*(t/V) = 1 := by dsimp [q]; field_simp
  have hvq : V/q = t := by dsimp [q]; field_simp
  suffices q ∈ functionExponents d (k+1) (N+1) by
    have hh := setExponent_of_functionExponent d k (N+1) this
    change V/q ∈ _ at hh
    rwa [hvq] at hh
  apply functionExponent_of_one_dimensional d k (N+1) hq
  intro f hf
  apply (bound_iff_weightedEnergy d k (N+1) 1 hq f hf).mpr
  let Z := ∑ x ∈ box 1 (N+1), f x ^ q
  let I := Finset.Ico 0 ((N+1:ℕ):ℤ)
  have hI : Z = ∑ j ∈ I, f (fun _ => j)^q := box_sum_int _ _
  by_cases hz : Z=0
  · have hzero : f=0 := by
      funext x
      by_cases hx : x∈box 1 (N+1)
      · have hs : f x^q=0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)).mp hz x hx
        exact (NNReal.rpow_eq_zero_iff.mp hs).1
      · exact hf x hx
    rw [hzero]
    have hB := (bound_iff_weightedEnergy d k (N+1) 1 hq (0:Lattice 1→ℝ≥0) (by simp)).mp
      (show gowers Measure.count d (k+1:ℕ) (0:Lattice 1→ℝ≥0) ≤ lp Measure.count q (liftNN 0) by
        rw [gowers_eq_weightedEnergy d k (∅:Finset (Lattice 1)) _ (by simp)]
        simp [weightedEnergy]
        rw [ENNReal.zero_rpow_of_pos (by positivity)]
        exact zero_le)
    exact hB
  let g (j : ℤ) := f (fun _ => j)^q / Z
  have hgm : ∑ j ∈ I, g j = 1 := by simp [g, ← Finset.sum_div, ← hI, hz]
  have hgs (j : ℤ) (hj : j∉I) : g j = 0 := by
    have hj' : (fun _ : Fin 1 => j) ∉ box 1 (N+1) := fun h => hj (Fintype.mem_piFinset.mp h 0)
    simp [g, hf _ hj', NNReal.zero_rpow hq.ne']
  let w (x : Lattice 1) := (g (x 0))^(t/V)
  let c := Z^(t/V)
  have hf' : f = fun x => c*w x := by
    funext x
    have he : (fun _ : Fin 1 => x 0) = x := by funext i; rw [Fin.eq_zero i]
    dsimp [c,w,g]
    rw [← NNReal.mul_rpow, show Z*(f (fun _ => x 0)^q/Z) = f (fun _ => x 0)^q by field_simp [hz], he, ← NNReal.rpow_mul, hqt, NNReal.rpow_one]
  have hE : weightedEnergy d (k+1) (box 1 (N+1)) w ≤ 1 := hbound g hgm hgs
  change _ ≤ Z ^ (V/q)
  rw [hf', weightedEnergy_scale, hvq]
  have hmass : c ^ (2^d*(k+1)) = Z^t := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    dsimp [V]; push_cast; field_simp
  rw [hmass]
  simpa using mul_le_mul_of_nonneg_left hE (show 0≤Z^t by positivity)



/-- Upper half of Theorem 1.5(c) with the exact binomial entropy coefficient,
the log-factorial term and an arbitrarily small additive error. -/
theorem entropy_largeDegree_upper (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ d : ℕ in atTop, criticalT d p n ≤ largeDegreeMainTerm n d + δ := by
  obtain ⟨N,rfl⟩ : ∃ N, n=N+1 := ⟨n-1, by omega⟩
  obtain ⟨k,rfl⟩ : ∃ k, p=k+1 := ⟨p-1, by omega⟩
  have hN : 1≤N := by omega
  have H := patternUpperSum_eventually N (k+1) hN hp δ hδ (activePatterns_card_le N)
  have hT := entropyMainTerm_tendsto N hN δ
  filter_upwards [H, hT.eventually_gt_atTop 0, eventually_ge_atTop N] with d Hd ht hNd
  apply (criticalT_isLeast d k (N+1) hn).2
  apply setExponent_of_normalized_energy N d k ht
  intro g hg hs
  apply (weightedEnergy_le_patternUpperSum hNd hp (largeDegreeMainTerm (N+1) d+δ) g _ _ (fun _ _ => rfl)).trans
    (Hd g hg)
  intro x hx
  have hxi : x 0 ∉ Finset.Ico 0 ((N+1:ℕ):ℤ) := by
    intro hi
    apply hx (Fintype.mem_piFinset.mpr _)
    intro j
    rwa [Fin.eq_zero j]
  rw [hs _ hxi, NNReal.zero_rpow (div_pos ht (by positivity)).ne']

/-- The full fixed-side, large-degree asymptotic in Theorem 1.5(c). -/
theorem largeDegreeClaim : LargeDegreeClaim := by
  intro n p hn hp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε/2 := by positivity
  filter_upwards [entropy_largeDegree_upper n p hn hp hδ,
    entropy_largeDegree_lower n p hn hp hδ] with d hi lo
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

end LpGowers.Discrete
