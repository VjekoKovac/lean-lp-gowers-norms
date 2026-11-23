module

public import LpGowers.DiscreteFunctional

/-! # Tensor powers and indicator estimates on integer cubes

Proposition 8.1 of arXiv:2609.08916v2 allows a dimension-independent constant
in a set estimate and then removes it by tensor powers.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal

namespace LpGowers.Discrete

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]

omit [DecidableEq G] [DecidableEq H] in
private theorem mem_map_addEquiv (e : G ≃+ H) (A : Finset G) (y : H) :
    y ∈ A.map e.toEquiv.toEmbedding ↔ e.symm y ∈ A :=
  Finset.mem_map_equiv

theorem baseCount_map (e : G ≃+ H) (A : Finset G) {d : ℕ} (h : Fin d → G) :
    baseCount (A.map e.toEquiv.toEmbedding) (fun i => e (h i)) = baseCount A h := by
  unfold baseCount
  rw [← Finset.card_map e.toEquiv.toEmbedding]
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_map_addEquiv, map_add, map_sum, AddEquiv.symm_apply_apply]

theorem energy_map (e : G ≃+ H) (A : Finset G) (d p : ℕ) :
    energy d p (A.map e.toEquiv.toEmbedding) = energy d p A := by
  let B := A.map e.toEquiv.toEmbedding
  have hdiff (y : H) : y ∈ B - B ↔ e.symm y ∈ A - A := by
    obtain ⟨x,rfl⟩ := e.surjective y
    simp only [AddEquiv.symm_apply_apply, Finset.mem_sub]
    constructor
    · rintro ⟨b,hb,c,hc,he⟩
      exact ⟨e.symm b, (mem_map_addEquiv e A _).1 hb, e.symm c, (mem_map_addEquiv e A _).1 hc,
        by simpa using congrArg e.symm he⟩
    · rintro ⟨b,hb,c,hc,rfl⟩
      exact ⟨e b,(mem_map_addEquiv e A _).2 (by simpa),e c,(mem_map_addEquiv e A _).2 (by simpa),
        (map_sub e b c).symm⟩
  unfold energy
  refine Finset.sum_bij' (fun h _ i => e.symm (h i)) (fun h _ i => e (h i)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact Fintype.mem_piFinset.mpr fun i => (hdiff _).mp (Fintype.mem_piFinset.mp hh i)
  · intro h hh
    apply Fintype.mem_piFinset.mpr
    exact fun i => (hdiff _).mpr (by simpa using Fintype.mem_piFinset.mp hh i)
  · intro h _; simp
  · intro h _; simp
  · intro h _
    have he := baseCount_map e A (fun i => e.symm (h i))
    simp only [AddEquiv.apply_symm_apply] at he
    rw [he]

/-- Flatten r copies of the m-dimensional lattice into dimension r*m. -/
private def flatten (r m : ℕ) : (Fin r → Lattice m) ≃+ Lattice (r*m) where
  toFun w j := w (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun z i j := z (finProdFinEquiv (i,j))
  left_inv w := by funext i j; simp
  right_inv z := by
    funext j
    exact congrArg z (finProdFinEquiv.apply_symm_apply j)
  map_add' _ _ := rfl

/-- A tensor power gives a test set in the original family of integer cubes. -/
theorem exists_tensor_test (d p n r m : ℕ) (A : Finset (Lattice m)) (hA : A ⊆ box m n) :
    ∃ B : Finset (Lattice (r*m)), B ⊆ box (r*m) n ∧ B.card = A.card ^ r ∧
      energy d p B = (energy d p A) ^ r := by
  let C := Fintype.piFinset (fun _ : Fin r => A)
  let e := flatten r m
  refine ⟨C.map e.toEquiv.toEmbedding, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    apply Fintype.mem_piFinset.mpr
    intro j
    have hv' := Fintype.mem_piFinset.mp hv (finProdFinEquiv.symm j).1
    exact Fintype.mem_piFinset.mp (hA hv') (finProdFinEquiv.symm j).2
  · simp [C]
  · rw [energy_map, energy_piFinset]
    simp

/-- Proposition 8.1(c) ⇔ (d). A constant independent of the ambient dimension
can be removed, with exactly the same exponent. -/
theorem setExponent_iff_uniform_constant (d k n : ℕ) {t : ℝ} (ht : 0 < t) :
    t ∈ setExponents d (k + 1) n ↔ ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (A : Finset (Lattice m)),
      A ⊆ box m n → (energy d (k + 1) A : ℝ) ≤ C * (A.card : ℝ) ^ t := by
  constructor
  · intro h
    exact ⟨1, zero_lt_one, fun m A hA => by simpa using h.2 m A hA⟩
  · rintro ⟨C, _, hC⟩
    refine ⟨ht, ?_⟩
    intro m A hA
    by_cases ha : A.card = 0
    · simpa [ha, Real.zero_rpow ht.ne'] using hC m A hA
    let u : ℝ := energy d (k + 1) A
    let v : ℝ := (A.card : ℝ) ^ t
    have hv : 0 < v := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero ha) _
    by_contra! hbad
    have : 1 < u / v := (one_lt_div hv).mpr hbad
    obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt C this
    obtain ⟨B, hB, hc, he⟩ := exists_tensor_test d (k+1) n r m A hA
    have htest := hC _ B hB
    rw [he, hc] at htest
    push_cast at htest
    have hpow : ((A.card : ℝ) ^ r) ^ t = v ^ r := by
      rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]
    rw [hpow] at htest
    rw [div_pow, lt_div_iff₀ (pow_pos hv _)] at hr
    exact (not_lt_of_ge htest) hr

/-- Finite-valued cube products for finite counting sums. -/
def finiteCubeProduct : (d : ℕ) → (G → ℝ≥0) → (Fin d → G) → G → ℝ≥0
  | 0, f, _, x => f x
  | d+1, f, h, x => finiteCubeProduct d f (Fin.tail h) x * finiteCubeProduct d f (Fin.tail h) (x+h 0)

/-- Finite power sum appearing when the common LCA functional is evaluated on a
function supported on A. -/
def weightedEnergy (d p : ℕ) (A : Finset G) (f : G → ℝ≥0) : ℝ≥0 :=
  ∑ h ∈ Fintype.piFinset (fun _ : Fin d => A-A), (∑ x ∈ A, finiteCubeProduct d f h x)^p

omit [DecidableEq G] in
private theorem coe_finiteCubeProduct (d : ℕ) (f : G → ℝ≥0) (h : Fin d → G) (x : G) :
    ((finiteCubeProduct d f h x : ℝ≥0) : ℝ≥0∞) = cubeProduct d f h x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp [cubeProduct, finiteCubeProduct, ih]

/-- A nonzero weighted cube product requires every vertex to lie in the supporting set. -/
theorem finiteCubeProduct_fits {A : Finset G} {f : G → ℝ≥0} (hf : ∀ x, x ∉ A → f x = 0)
    (d : ℕ) (h : Fin d → G) (x : G) (hne : finiteCubeProduct d f h x ≠ 0) : fits A h x := by
  induction d generalizing x with
  | zero =>
    have hx : x ∈ A := by by_contra hh; exact hne (hf x hh)
    intro s
    have hs : s = ∅ := Subsingleton.elim _ _
    simpa [hs] using hx
  | succ d ih =>
    have hh := mul_ne_zero_iff.mp hne
    rw [← Fin.cons_self_tail h]
    apply (fits_cons A _ _ _).mpr
    exact ⟨ih _ _ hh.1, ih _ _ hh.2⟩

open MeasureTheory
open scoped NNReal ENNReal
variable [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]

/-- Finite-counting formula for every nonnegative finitely supported function and
every positive integer p; indicators are not required. -/
theorem gowers_eq_weightedEnergy (d k : ℕ) (A : Finset G) (f : G → ℝ≥0)
    (hf : ∀ x, x ∉ A → f x = 0) :
    gowers Measure.count d (k+1 : ℕ) f =
      ((weightedEnergy d (k+1) A f : ℝ≥0) : ℝ≥0∞) ^ (1/((2:ℝ)^d * (k+1 : ℕ))) := by
  let H := Fintype.piFinset (fun _ : Fin d => A-A)
  have hR (h : Fin d → G) : autocorrelation Measure.count d f h =
      ((∑ x ∈ A, finiteCubeProduct d f h x : ℝ≥0) : ℝ≥0∞) := by
    rw [autocorrelation, lintegral_count, tsum_eq_sum (s := A)]
    · simp [coe_finiteCubeProduct]
    · intro x hx
      rw [← coe_finiteCubeProduct]
      suffices finiteCubeProduct d f h x = 0 by simp [this]
      by_contra hn
      have := finiteCubeProduct_fits hf d h x hn ∅
      exact hx (by simpa using this)
  have hw : ∫⁻ h : Fin d → G, autocorrelation Measure.count d f h ^ (k+1 : ℕ)
       ∂Measure.count = ((weightedEnergy d (k+1) A f : ℝ≥0) : ℝ≥0∞) := by
    rw [lintegral_count, tsum_eq_sum (s := H)]
    · simp [hR, weightedEnergy, H]
    · intro h hh
      have hz (x : G) : finiteCubeProduct d f h x = 0 := by
        by_contra hn
        have hfit := finiteCubeProduct_fits hf d h x hn
        have hxA : x ∈ A := by simpa using hfit ∅
        have hpos : 0 < baseCount A h := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxA,hfit⟩⟩
        exact hpos.ne' (baseCount_eq_zero_outside A h hh)
      simp [hR, hz]
  simp only [gowers, lp, cubeMeasure_count, ENNReal.rpow_natCast, hw, ← ENNReal.rpow_mul]
  congr 1
  simp [one_div, mul_inv_rev]

omit [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G] [DecidableEq G] in
private theorem finiteCubeProduct_tensor {m : ℕ} (d : ℕ) (f : Fin m → G → ℝ≥0)
    (h : Fin d → Fin m → G) (x : Fin m → G) :
    finiteCubeProduct d (fun y => ∏ j, f j (y j)) h x = ∏ j, finiteCubeProduct d (f j) (fun i => h i j) (x j) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    simp only [finiteCubeProduct, ih, Finset.prod_mul_distrib, Pi.add_apply]
    rfl

omit [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G] in
/-- The complete finite weighted functional tensorizes on pure tensors in
arbitrary dimensions, including non-indicator functions. -/
theorem weightedEnergy_piFinset {m : ℕ} (d p : ℕ) (A : Fin m → Finset G) (f : Fin m → G → ℝ≥0) :
    weightedEnergy d p (Fintype.piFinset A) (fun y => ∏ j, f j (y j)) =
      ∏ j, weightedEnergy d p (A j) (f j) := by
  classical
  unfold weightedEnergy
  rw [← Fintype.piFinset_sub, Finset.prod_univ_sum]
  refine Finset.sum_bij' (fun h _ j i => h i j) (fun h _ i j => h j i) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact Fintype.mem_piFinset.mpr (fun j => Fintype.mem_piFinset.mpr
      (fun i => Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hh i) j))
  · intro h hh
    exact Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mpr
      (fun j => Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hh j) i))
  · intros; rfl
  · intros; rfl
  · intro h _
    simp only [finiteCubeProduct_tensor]
    rw [← Finset.prod_univ_sum, Finset.prod_pow]

omit [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G] in
theorem weightedEnergy_map (e : G ≃+ H) (A : Finset G) (f : G → ℝ≥0) (d p : ℕ) :
    weightedEnergy d p (A.map e.toEquiv.toEmbedding) (fun y => f (e.symm y)) =
      weightedEnergy d p A f := by
  have hc (j : ℕ) (h : Fin j → H) (x : G) :
      finiteCubeProduct j (fun y => f (e.symm y)) h (e x) =
      finiteCubeProduct j f (fun i => e.symm (h i)) x := by
    induction j generalizing x with
    | zero => simp [finiteCubeProduct]
    | succ j ih =>
      simp only [finiteCubeProduct]
      rw [show e x + h 0 = e (x + e.symm (h 0)) by simp, ih, ih]
      rfl
  unfold weightedEnergy
  have hd : (A.map e.toEquiv.toEmbedding) - (A.map e.toEquiv.toEmbedding) =
      (A-A).map e.toEquiv.toEmbedding := by
    simp only [Finset.map_eq_image]
    exact (Finset.image_image₂_distrib (s := A) (t := A) (map_sub e)).symm
  rw [hd]
  refine Finset.sum_bij' (fun h _ i => e.symm (h i)) (fun h _ i => e (h i)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    exact Fintype.mem_piFinset.mpr fun i => (mem_map_addEquiv e _ _).mp (Fintype.mem_piFinset.mp hh i)
  · intro h hh
    apply Fintype.mem_piFinset.mpr
    exact fun i => (mem_map_addEquiv e _ _).mpr (by simpa using Fintype.mem_piFinset.mp hh i)
  · intros; simp
  · intros; simp
  · intro h _
    simp [Finset.sum_map, hc]

/-- R-fold tensor test functions on side-n cubes: both the powered functional and
the q-power sum are multiplicative, with no loss. -/
theorem exists_weighted_tensor_test (m n r d p : ℕ) (f : Lattice m → ℝ≥0)
    (hf : ∀ x, x ∉ box m n → f x = 0) (q : ℝ) :
    ∃ g : Lattice (r*m) → ℝ≥0, (∀ x, x ∉ box (r*m) n → g x = 0) ∧
      weightedEnergy d p (box (r*m) n) g = (weightedEnergy d p (box m n) f)^r ∧
      ∑ x ∈ box (r*m) n, g x ^ q = (∑ x ∈ box m n, f x ^ q)^r := by
  let A := box m n
  let C := Fintype.piFinset (fun _ : Fin r => A)
  let e := flatten r m
  let g (x : Lattice (r*m)) := ∏ i, f (e.symm x i)
  have hbox : C.map e.toEquiv.toEmbedding = box (r*m) n := by
    ext z
    rw [mem_map_addEquiv]
    constructor
    · intro hz
      apply Fintype.mem_piFinset.mpr
      intro u
      have h := Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hz (finProdFinEquiv.symm u).1) (finProdFinEquiv.symm u).2
      change z (finProdFinEquiv (finProdFinEquiv.symm u)) ∈ _ at h
      exact (finProdFinEquiv.apply_symm_apply u) ▸ h
    · intro hz
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Fintype.mem_piFinset.mpr (fun j => Fintype.mem_piFinset.mp hz (finProdFinEquiv (i,j)))
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    have hx : e.symm z ∉ C := by simpa [← hbox, mem_map_addEquiv] using hz
    obtain ⟨i,hi⟩ : ∃ i, e.symm z i ∉ A := by simpa [C] using hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hf _ hi)
  · rw [← hbox]
    change weightedEnergy d p (C.map e.toEquiv.toEmbedding) (fun z => (fun y => ∏ i, f (y i)) (e.symm z)) = _
    rw [weightedEnergy_map e C (fun y => ∏ i : Fin r, f (y i)) d p, weightedEnergy_piFinset]
    simp [A]
  · rw [← hbox, Finset.sum_map]
    change (∑ x ∈ C, (∏ i, f (e.symm (e x) i))^q) = _
    simp only [AddEquiv.symm_apply_apply, ← NNReal.finsetProd_rpow]
    change (∑ x ∈ Fintype.piFinset (fun _ : Fin r => A), _) = _
    exact (Finset.sum_pow' A (fun x => f x ^ q) r).symm


/-- The finite power-sum formulation of the estimate for a single test function. -/
theorem bound_iff_weightedEnergy (d k n m : ℕ) {q : ℝ} (hq : 0 < q)
    (f : Lattice m → ℝ≥0) (hf : ∀ x, x ∉ box m n → f x = 0) :
    gowers Measure.count d (k+1 : ℕ) f ≤ lp Measure.count q (liftNN f) ↔
      weightedEnergy d (k+1) (box m n) f ≤
        (∑ x ∈ box m n, f x ^ q) ^ ((2 : ℝ)^d * (k+1 : ℕ) / q) := by
  rw [gowers_eq_weightedEnergy d k _ f hf, lp_count_finite _ f hf hq,
    ← ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_le_coe, one_div,
    NNReal.rpow_inv_le_iff (by positivity), ← NNReal.rpow_mul]
  simp only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm]

open Filter

/-- The polynomial loss in (8.3) disappears under tensor powers. The hypothesis
is stated for the finite power sums, where the exponent on the q-power sum
is t=p2^d/q. Both the exponent s of the polynomial loss and C may be fixed arbitrarily. -/
theorem functionExponent_of_polynomial_loss (d k n : ℕ) {q : ℝ} (hq : 0 < q)
    (C : ℝ) (hC : 0 < C) (s : ℕ)
    (hh : ∀ (m : ℕ) (f : Lattice m → ℝ≥0), (∀ x, x ∉ box m n → f x = 0) →
      (weightedEnergy d (k+1) (box m n) f : ℝ) ≤ C * ((m : ℝ) + 1)^s *
        ((∑ x ∈ box m n, f x ^ q : ℝ≥0) : ℝ) ^ ((2 : ℝ)^d * (k+1 : ℕ) / q)) :
    q ∈ functionExponents d (k+1) n := by
  refine ⟨hq, ?_⟩
  intro m f hf
  apply (bound_iff_weightedEnergy d k n m hq f hf).mpr
  let t : ℝ := (2 : ℝ)^d * (k+1 : ℕ) / q
  let z : ℝ := (∑ x ∈ box m n, f x ^ q : ℝ≥0)
  let u : ℝ := weightedEnergy d (k+1) (box m n) f
  let v : ℝ := z^t
  have hz : 0 ≤ z := NNReal.zero_le_coe
  change u ≤ v
  have hbase : u ≤ C * ((m : ℝ)+1)^s * v := hh m f hf
  by_cases hv : v = 0
  · simpa [hv] using hbase
  have hpos : 0 < v := lt_of_le_of_ne (Real.rpow_nonneg hz _) (Ne.symm hv)
  by_contra! hbad
  let a := u/v
  have ha : 1 < a := (one_lt_div hpos).mpr hbad
  have Hpow (r : ℕ) : u^r ≤ C * ((r:ℝ)*m + 1)^s * v^r := by
    obtain ⟨g,hg,hu,hv'⟩ := exists_weighted_tensor_test m n r d (k+1) f hf q
    have htest := hh _ g hg
    rw [hu,hv'] at htest
    simp only [NNReal.coe_pow, Nat.cast_mul] at htest
    have hp : (z ^ r)^t = v^r := by
      rw [← Real.rpow_natCast_mul hz, mul_comm, Real.rpow_mul_natCast hz]
    change u^r ≤ C * ((r:ℝ)*m + 1)^s * (z^r)^t at htest
    simpa only [hp] using htest
  have hevent : ∀ᶠ r : ℕ in atTop, 1 ≤ C * ((m : ℝ)+1)^s * ((r:ℝ)^s/a^r) := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr' : 1 ≤ (r:ℝ) := by exact_mod_cast hr
    have hpoly : ((r:ℝ)*m+1)^s ≤ ((m:ℝ)+1)^s*(r:ℝ)^s := by
      rw [← mul_pow]
      gcongr
      linarith
    have hrat : a^r ≤ C * ((r:ℝ)*m+1)^s := by
      rw [show a^r = u^r/v^r by rw [div_pow], div_le_iff₀ (pow_pos hpos _)]
      exact Hpow r
    rw [← mul_div_assoc, le_div_iff₀ (pow_pos (zero_lt_one.trans ha) _), one_mul, mul_assoc]
    exact hrat.trans (mul_le_mul_of_nonneg_left hpoly hC.le)
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt s ha).const_mul (C*((m:ℝ)+1)^s)
  have hfalse : (1 : ℝ) ≤ 0 := by simpa using ge_of_tendsto hlim hevent
  norm_num at hfalse

end LpGowers.Discrete
