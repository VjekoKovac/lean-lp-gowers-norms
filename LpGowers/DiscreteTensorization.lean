module

public import LpGowers.DiscreteConfigurations
public import LpGowers.DiscreteMixed

/-! # Dimension induction for the discrete product principle

Each one-dimensional outer configuration indexes slices of the input. The
inner multilinear Gowers inequality bounds the sum of products of slices,
after which the induction hypothesis supplies their ℓᵠ norms. The remaining
sum is the one-dimensional inequality for the function of slice norms.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LpGowers.Discrete

theorem homogeneous_configurationSum {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G] (d k : ℕ) (f : G → ℝ≥0) :
    configurationSum d (k+1) (fun _ _ => liftNN f) =
      gowers Measure.count d (k+1:ℕ) f ^ ((2:ℝ)^d*(k+1:ℕ)) := by
  rw [tsum_configurations,gowers_count_nat_mass]
  apply tsum_congr
  intro h
  simp only [liftNN,← cubeProduct_vertices,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- A countable lattice slice has finite ℓᵠ norm because the whole input is
supported on a finite box. -/
private theorem lattice_slice_norm {m n : ℕ} {q : ℝ} (hq : 0<q)
    (f : Lattice (m+1) → ℝ≥0) (hs : ∀ x,x∉box (m+1) n → f x=0) :
    let R := fun b x => f (joinLattice m (b,x))
    let N := fun b => (lp Measure.count q (liftNN (R b))).toNNReal
    (∀ b x, x∉box m n → R b x=0) ∧ (∀ b, b∉box 1 n → N b=0) ∧
    (∀ b, (N b:ℝ≥0∞)=lp Measure.count q (liftNN (R b))) ∧
    lp Measure.count q (liftNN N)=lp Measure.count q (liftNN f) := by
  intro R N
  have hR (b : Lattice 1) (x : Lattice m) (hx : x∉box m n) : R b x=0 := by
    apply hs
    intro h
    exact hx ((joinLattice_mem_box m n b x).mp h).2
  have hfin (b) : (N b:ℝ≥0∞)=lp Measure.count q (liftNN (R b)) := by
    apply ENNReal.coe_toNNReal
    rw [lp_count_finite (box m n) (R b) (hR b) hq]
    exact ENNReal.coe_ne_top
  have hNor (b : Lattice 1) (hb : b∉box 1 n) : N b=0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [hfin,lp]
    have hzero (x : Lattice m) : R b x=0 :=
      hs _ (fun h => hb ((joinLattice_mem_box m n b x).mp h).1)
    simp [liftNN,hzero,hq]
  refine ⟨hR,hNor,hfin,?_⟩
  simp only [lp,liftNN,lintegral_count]
  congr 1
  have inner (b) : (N b:ℝ≥0∞)^q = ∑' x, (R b x:ℝ≥0∞)^q := by
    rw [hfin,lp,lintegral_count,← ENNReal.rpow_mul,one_div_mul_cancel hq.ne',ENNReal.rpow_one]
    rfl
  simp_rw [inner]
  calc
    _ = ∑' z : Lattice 1 × Lattice m, (R z.1 z.2 : ℝ≥0∞)^q := tsum_prod.symm
    _ = _ := (joinLattice m).toEquiv.tsum_eq (fun z => (f z : ℝ≥0∞)^q)

/-- The zero-dimensional case of the product induction, including zero
inputs. Both positive-exponent quantities equal the value at the single
lattice point. -/
private theorem dimension_zero_bound (d k : ℕ) {q : ℝ} (hq : 0<q) (f : Lattice 0 → ℝ≥0) :
    gowers Measure.count d (k+1:ℕ) f ≤ lp Measure.count q (liftNN f) := by
  let c : ℝ≥0∞ := f default
  have hf (x : Lattice 0) : (f x : ℝ≥0∞)=c := congrArg (fun z => (f z:ℝ≥0∞)) (Subsingleton.elim x default)
  have hq' : lp Measure.count q (liftNN f)=c := by
    simp only [lp,liftNN,lintegral_count,tsum_fintype,Fintype.sum_unique,hf,one_div,
      ENNReal.rpow_rpow_inv hq.ne']
  rw [hq']
  have hP : 0<(2:ℝ)^d*(k+1:ℕ) := by positivity
  apply (ENNReal.rpow_le_rpow_iff hP).mp
  rw [← homogeneous_configurationSum]
  let : Unique (CubeConfigurations (Lattice 0) d (k+1)) :=
    ⟨⟨default⟩, fun x => Subsingleton.elim x _⟩
  simp only [configurationSum, liftNN, hf, Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_finset,tsum_fintype,Fintype.sum_unique,← pow_mul]
  rw [← ENNReal.rpow_natCast]
  norm_cast

/-- Proposition 8.1(a) implies (b), using the shared-increment multilinear
inequality for the inner slices. -/
theorem functionExponent_of_one_dimensional_of_mixed (d k n : ℕ) {q : ℝ} (hq : 0<q)
    (hone : ∀ f : Lattice 1 → ℝ≥0, (∀ x,x∉box 1 n → f x=0) →
      gowers Measure.count d (k+1:ℕ) f ≤ lp Measure.count q (liftNN f))
    (hmix : ∀ (m : ℕ) (F : Fin (k+1) → Finset (Fin d) → Lattice m → ℝ≥0),
      (∑' h : Fin d → Lattice m, ∏ j, ∑' x : Lattice m, ∏ s : Finset (Fin d),
        (F j s (x+∑ i ∈ s,h i):ℝ≥0∞)) ≤ ∏ j, ∏ s, gowers Measure.count d (k+1:ℕ) (F j s)) :
    q ∈ functionExponents d (k+1) n := by
  refine ⟨hq,?_⟩
  intro m
  induction m with
  | zero => exact fun f _ => dimension_zero_bound d k hq f
  | succ m ih =>
    intro f hsup
    let e := joinLattice m
    let R := fun b x => f (e (b,x))
    let N := fun b => (lp Measure.count q (liftNN (R b))).toNNReal
    obtain ⟨hR,hN,hNval,hNq⟩ := lattice_slice_norm hq f hsup
    have hP : 0<(2:ℝ)^d*(k+1:ℕ) := by positivity
    apply (ENNReal.rpow_le_rpow_iff hP).mp
    rw [← homogeneous_configurationSum,configurationSum_split e d (k+1) (liftNN f)]
    calc
      _ ≤ configurationSum d (k+1) (fun _ _ => liftNN N) := by
        apply tsum_le_tsum
        intro z
        let F := fun j s => R (configurationVertex z j s)
        change configurationSum d (k+1) (fun j s => liftNN (F j s)) ≤ ∏ j, ∏ s, (N (configurationVertex z j s):ℝ≥0∞)
        rw [tsum_configurations]
        refine (hmix m F).trans ?_
        apply Finset.prod_le_prod
        intro j _
        apply Finset.prod_le_prod
        intro s _
        change gowers Measure.count d (k+1:ℕ) (R (configurationVertex z j s)) ≤ (N _:ℝ≥0∞)
        rw [hNval]
        exact ih _ (hR _)
      _ = gowers Measure.count d (k+1:ℕ) N ^ ((2:ℝ)^d*(k+1:ℕ)) := homogeneous_configurationSum ..
      _ ≤ lp Measure.count q (liftNN N) ^ ((2:ℝ)^d*(k+1:ℕ)) :=
        ENNReal.rpow_le_rpow (hone N hN) hP.le
      _ = _ := congrArg (fun v : ℝ≥0∞ => v ^ ((2:ℝ)^d*(k+1:ℕ))) hNq

/-- The sharp one-dimensional functional inequality tensorizes to every
integer lattice, including dimension zero. -/
theorem functionExponent_of_one_dimensional (d k n : ℕ) {q : ℝ} (hq : 0<q)
    (hone : ∀ f : Lattice 1 → ℝ≥0, (∀ x,x∉box 1 n → f x=0) →
      gowers Measure.count d (k+1:ℕ) f ≤ lp Measure.count q (liftNN f)) :
    q ∈ functionExponents d (k+1) n :=
  functionExponent_of_one_dimensional_of_mixed d k n hq hone (fun _ => mixed_count_holder d k)

end LpGowers.Discrete
