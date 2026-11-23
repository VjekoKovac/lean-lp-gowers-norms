module

public import LpGowers.ConfigurationRiemann
public import LpGowers.DiscreteTriangle

/-! # The critical inequality on samples of a test function

For tests between zero and one, the attained functional exponent is at
least its limiting value `2^d p/(d+p)`. Consequently both Riemann sums
may use fixed continuous integrands, even while the optimal exponent of
the outer test inequality varies with the side length. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace LpGowers.Discrete

/-- Sampling a one-dimensional function on the integer lattice. -/
def latticeSample (f : ℝ → ℝ≥0) (n : ℕ) (z : Lattice 1) := f (gridPoint n z 0)

private def packLattice (d p : ℕ) : (Fin d ⊕ Fin p → ℤ) ≃ CubeConfigurations (Lattice 1) d p where
  toFun z := (fun i _ => z (.inl i),fun j _ => z (.inr j))
  invFun z := Sum.elim (fun i => z.1 i 0) (fun j => z.2 j 0)
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by
    apply Prod.ext <;> funext i j <;> rw [Fin.eq_zero j] <;> rfl

private theorem sampled_vertex (d p n : ℕ) (z : Fin d ⊕ Fin p → ℤ) (j : Fin p) (s : Finset (Fin d)) :
    gridPoint n (configurationVertex (packLattice d p z) j s) 0 =
      packedVertex (gridPoint n z) j s := by
  simp [gridPoint,configurationVertex,packedVertex,packLattice,Finset.sum_apply,add_div,Finset.sum_div]

private theorem sample_numerator (d k n : ℕ) (f : ℝ → ℝ≥0) :
    ((gowers Measure.count d (k+1:ℕ) (latticeSample f n))^((2:ℝ)^d*(k+1:ℕ))).toReal =
    ∑' z : Fin d ⊕ Fin (k+1) → ℤ, realCubeDensity d (k+1) f (gridPoint n z) := by
  rw [← homogeneous_configurationSum,configurationSum,
    ← (packLattice d (k+1)).tsum_eq (fun z => ∏ j, ∏ s, liftNN (latticeSample f n) (configurationVertex z j s))]
  rw [ENNReal.tsum_toReal_eq]
  rotate_left
  · intro z
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.prod_ne_top (fun _ _ => ENNReal.coe_ne_top))
  apply tsum_congr
  intro z
  simp only [ENNReal.toReal_prod,liftNN,ENNReal.coe_toReal,latticeSample,sampled_vertex,realCubeDensity]

private theorem sampled_support {n : ℕ} (hn : 0<n) {f : ℝ → ℝ≥0}
    (hs : Function.support f ⊆ Set.Ioo 0 1) :
    ∀ x,x ∉ box 1 n → latticeSample f n x=0 := by
  intro x hx
  contrapose! hx
  have h := hs hx
  change (0:ℝ) < (x 0:ℝ)/n ∧ (x 0:ℝ)/n < 1 at h
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have h0 : (0:ℝ)<x 0 := (div_pos_iff_of_pos_right hN).mp h.1
  have h1 : (x 0:ℝ)<n := by simpa using (div_lt_iff₀ hN).mp h.2
  refine Fintype.mem_piFinset.mpr fun i => ?_
  rw [Fin.eq_zero i,Finset.mem_Ico]
  exact ⟨by exact_mod_cast h0.le,by exact_mod_cast h1⟩

private theorem sampled_q_limit {q : ℝ} (hq : 0<q) {f : ℝ → ℝ≥0} (hf : Continuous f)
    (hs : Function.support f ⊆ Set.Ioo 0 1) :
    Tendsto (fun n : ℕ => ((lp Measure.count q (liftNN (latticeSample f n)))^q).toReal/n)
      atTop (𝓝 ((lp volume q (liftNN f))^q).toReal) := by
  let F := fun z : Fin 1 → ℝ => ((f (z 0):ℝ)^q)
  have hF : Continuous F := by dsimp [F]; fun_prop (disch := positivity)
  let S : Set (Fin 1 → ℝ) := Set.Icc 0 1
  have hzero (z : Fin 1 → ℝ) (hz : z ∉ S) : F z=0 := by
    have h : f (z 0)=0 := by
      contrapose! hz
      have hh := hs hz
      exact ⟨fun i => Fin.eq_zero i ▸ hh.1.le,fun i => Fin.eq_zero i ▸ hh.2.le⟩
    simp [F,h,hq.ne']
  have h := tendsto_lattice_sum S F hF isCompact_Icc.isBounded measurableSet_Icc
    ((convex_Icc ..).addHaar_frontier volume) hzero
  have hlim : (∫ z, F z)=((lp volume q (liftNN f))^q).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f:=F) (Eventually.of_forall fun z => Real.rpow_nonneg (f (z 0)).coe_nonneg _)
      hF.aestronglyMeasurable]
    simp only [F,← ENNReal.ofReal_rpow_of_nonneg (f _).coe_nonneg hq.le,ENNReal.ofReal_coe_nnreal,
      lp,← ENNReal.rpow_mul,one_div_mul_cancel hq.ne',ENNReal.rpow_one,liftNN]
    congr 1
    exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp (f:=fun x => (f x:ℝ≥0∞)^q)
      ((hf.measurable.coe_nnreal_ennreal).pow_const q)
  rw [hlim] at h
  refine h.congr (fun n => ?_)
  simp only [Fintype.card_fin,pow_one,lp,← ENNReal.rpow_mul,one_div_mul_cancel hq.ne',ENNReal.rpow_one,
    lintegral_count,ENNReal.tsum_toReal_eq (fun z => ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top),
    ← ENNReal.toReal_rpow,liftNN, ENNReal.coe_toReal,latticeSample,F]

/-- Riemann-sum tests for the defect of the sharp interval exponent. The
limiting masses retain their exact Gowers and Lebesgue normalizations. -/
theorem exists_lattice_riemann_samples (d k : ℕ) (_hd : 2≤d) {f : ℝ → ℝ≥0} (hf : Continuous f)
    (hs : Function.support f ⊆ Set.Ioo 0 1) (hb : ∀ x,f x≤1) :
    let N := (2:ℝ)^d*(k+1:ℕ)
    let q := criticalExponent d (k+1:ℕ)
    ∃ A B : ℕ → ℝ, Tendsto A atTop (𝓝 ((gowers volume d (k+1:ℕ) f)^N).toReal) ∧
      Tendsto B atTop (𝓝 ((lp volume q (liftNN f))^q).toReal) ∧
      ∀ᶠ n : ℕ in atTop, (n:ℝ)^(d+(k+1))*A n ≤ ((n:ℝ)*B n)^(criticalT d (k+1) n) := by
  intro N q
  have hN : 0<N := by dsimp [N]; positivity
  have hq : 0<q := by dsimp [q,criticalExponent]; positivity
  let A := fun n : ℕ => ((gowers Measure.count d (k+1:ℕ) (latticeSample f n))^N).toReal/(n:ℝ)^(d+(k+1))
  let B := fun n : ℕ => ((lp Measure.count q (liftNN (latticeSample f n)))^q).toReal/n
  refine ⟨A,B,?_,sampled_q_limit hq hf hs,?_⟩
  · have h := tendsto_sampled_configuration d k hf hs
    have hsum : (∫ z, realCubeDensity d (k+1) f z) = ((gowers volume d (k+1:ℕ) f)^N).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (f := realCubeDensity d (k+1) f)
        (Eventually.of_forall fun z => Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => (f _).coe_nonneg)))
        (continuous_realCubeDensity d (k+1) hf).aestronglyMeasurable,continuous_configuration_moment d k hf]
    rw [hsum] at h
    refine h.congr (fun n => ?_)
    rw [← sample_numerator]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let Q := criticalQ d (k+1) n
    let t := criticalT d (k+1) n
    let g := latticeSample f n
    have hne : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    have hQt : Q*t=N := critical_product d k n hn
    have hQadm := (criticalQ_isGreatest d k n hn).1
    have hQ : 0<Q := hQadm.1
    have ht : 0<t := (criticalT_isLeast d k n hn).1.1
    have hbound : q≤Q := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<d+(k+1:ℕ))).mpr
      rw [show (2:ℝ)^d*(k+1:ℕ)=N by rfl,← hQt]
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add] using criticalT_le_add d k n) hQ.le
    have hge := hQadm.2 1 g (sampled_support (by omega) hs)
    have hpow := ENNReal.rpow_le_rpow hge hN.le
    have hsimp : 1/Q*N = t := by rw [←hQt]; field_simp
    have hR : (gowers Measure.count d (k+1:ℕ) g)^N ≤ (∫⁻ z, (g z:ℝ≥0∞)^q ∂Measure.count)^t := by
      unfold lp at hpow
      rw [← ENNReal.rpow_mul,hsimp] at hpow
      exact hpow.trans (ENNReal.rpow_le_rpow (lintegral_mono fun z => ENNReal.rpow_le_rpow_of_exponent_ge
        (show (g z:ℝ≥0∞)≤1 by exact_mod_cast hb _) hbound) ht.le)
    have hfint : (∫⁻ z, (g z : ℝ≥0∞)^q ∂Measure.count) ≠ ⊤ := by
      have he : (lp Measure.count q (liftNN g))^q=∫⁻ z, (g z:ℝ≥0∞)^q ∂Measure.count := by
        simp [lp,liftNN,← ENNReal.rpow_mul,hq.ne']
      rw [← he,lp_count_finite (box 1 n) g (sampled_support (by omega) hs) hq]
      exact ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top
    have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg ht.le hfint) hR
    dsimp only [A,B]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hne),mul_div_cancel₀ _ hne]
    simpa only [lp,liftNN,← ENNReal.rpow_mul,one_div_mul_cancel hq.ne',ENNReal.rpow_one,ENNReal.toReal_rpow] using h

end LpGowers.Discrete
