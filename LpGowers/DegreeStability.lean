module

public import LpGowers.DegreeNearForward
public import LpGowers.DegreeNearReverse
public import LpGowers.LWFactorization

/-! # From the joint density to a common family of one-dimensional factors

Near equality in Loomis–Whitney supplies factors for the normalized face
densities. Telescoping transfers their approximation to the joint density.
All thresholds are chosen before the group, its measure and the function.
-/

public section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LpGowers

private theorem small_lw_tolerance (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ tol : ℝ, 0 < tol ∧ tol ≤ η ∧
      2*(j+2:ℕ)*(ENNReal.ofReal tol)^(1/((j:ℝ)+1)) ≤ ENNReal.ofReal (η/2) := by
  let s := η/(4*((j:ℝ)+2))
  have hs : 0 < s := by dsimp [s]; positivity
  have hj : 0 < (j:ℝ)+1 := by positivity
  let tol := min η (s ^ ((j:ℝ)+1))
  refine ⟨tol,lt_min hη (Real.rpow_pos_of_pos hs _),min_le_left _ _,?_⟩
  have small : (ENNReal.ofReal tol)^(1/((j:ℝ)+1)) ≤ ENNReal.ofReal s := by
    have hb := ENNReal.ofReal_le_ofReal (min_le_right η (s ^ ((j:ℝ)+1)))
    apply (ENNReal.rpow_le_rpow hb (by positivity : 0 ≤ 1/((j:ℝ)+1))).trans_eq
    rw [← ENNReal.ofReal_rpow_of_pos hs,← ENNReal.rpow_mul,mul_one_div_cancel hj.ne',ENNReal.rpow_one]
  calc
    _ ≤ 2*(j+2:ℕ)* ENNReal.ofReal s := mul_le_mul_right small _
    _ = _ := by
      rw [show (2:ℝ≥0∞)*(j+2:ℕ)=ENNReal.ofReal (2*((j:ℝ)+2)) by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num [ENNReal.ofReal_add, Nat.cast_nonneg],
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [s]
      field_simp
      ring

/-- This tolerance depends only on the degree and desired accuracy. It
converts normalized joint-to-face closeness to both source conclusions. -/
theorem degreeApproximation_of_jointFaceError (j : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (G : Type u) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
      (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ] (p : ℝ) (q : Fin (j+2) → ℝ)
      (f : G → ℝ≥0), 0 < p → (∀ i, 0 < q i) → AEMeasurable f μ →
      (0 < gowers μ (j+2) p f ∧ gowers μ (j+2) p f < ⊤) →
      (∀ i, 0 < gowers μ (j+1) (q i) f ∧ gowers μ (j+1) (q i) f < ⊤) →
      jointFaceError μ j p q f ≤ ENNReal.ofReal ρ → DegreeApproximation μ (j+1) p q f η := by
  obtain ⟨tol,htol,htolη,htolpow⟩ := small_lw_tolerance j hη
  obtain ⟨σ,hσ,Hlw⟩ := lw_stability j htol
  let ρ := min (σ/2) (η/2)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  refine ⟨ρ,hρ,?_⟩
  intro G _ _ _ μ _ _ p q f hp hq hf hJ hI hclose
  let ν := cubeMeasure μ (j+2)
  let ν' := cubeMeasure μ (j+1)
  let M := autocorrelation μ (j+1) f
  let F := autocorrelation μ (j+2) f
  let A := fun i => momentDensity ν' (q i) M
  let W := momentDensity ν p F
  have hm := measurable_autocorrelation_of_aemeasurable μ (j+1) hf
  have hW : Measurable W := momentDensity_measurable ν p (measurable_autocorrelation_of_aemeasurable μ (j+2) hf)
  have hA i : Measurable (A i) := momentDensity_measurable ν' _ hm
  have hw : (∫⁻ x,W x ∂ν) = 1 := momentDensity_integral _ _
    (measurable_autocorrelation_of_aemeasurable μ (j+2) hf) (moment_regular_of_gowers μ _ hp hJ).1
    (moment_regular_of_gowers μ _ hp hJ).2
  have hmass : ENNReal.ofReal (1-ρ) ≤ ∫⁻ x, lwProduct j A x ∂ν := by
    rw [ENNReal.ofReal_sub _ hρ.le,ENNReal.ofReal_one]
    exact tsub_le_iff_tsub_le.mp ((one_sub_lintegral_le_l1 ν hW (lwProduct_measurable hA) hw).trans hclose)
  have hAm i : (∫⁻ y,A i y ∂ν') = 1 := momentDensity_integral ν' _ hm
    (moment_regular_of_gowers μ _ (hq i) (hI i)).1 (moment_regular_of_gowers μ _ (hq i) (hI i)).2
  have hρσ : ρ < σ := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨r,hr,herr⟩ := Hlw ρ hρ.le hρσ μ A hA hAm hmass
  apply degreeApproximation_of_normalized_densities μ j hp hq hf hJ hI r hr
      (ENNReal.ofReal tol) (ENNReal.ofReal ρ) (ENNReal.ofReal_le_ofReal htolη) _ hclose herr
  have hρη : ρ ≤ η/2 := min_le_right _ _
  apply (add_le_add (ENNReal.ofReal_le_ofReal hρη) htolpow).trans_eq
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]

/-- Theorem 1.4(b), with uniform thresholds in both parameter regimes. -/
theorem degree_stability : DegreeStability.{u} := by
  intro k hk p q θ hpar hp_ne η hη
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨ρ,hρ,Hfinish⟩ := degreeApproximation_of_jointFaceError.{u} j hη
  by_cases hfor : DegreeForward p θ
  · obtain ⟨δ,hδ,H⟩ := degree_forward_near.{u} j hpar hfor hp_ne hρ
    refine ⟨δ,hδ,?_⟩
    intro ε he hε G _ _ _ _ _ _ _ _ μ _ f hf
    dsimp only
    intro hJ₀ hJt hI hn
    rcases hn with ⟨_,hn⟩ | ⟨hr,_⟩
    · exact Hfinish G μ p q f hfor.1 hpar.1 hf ⟨hJ₀,hJt⟩ hI
        (H ε he hε G μ f hf ⟨hJ₀,hJt⟩ hI hn)
    · exact ((not_lt.mpr hfor.2.1) hr.1).elim
  · by_cases hrev : DegreeReverse p θ
    · obtain ⟨δ,hδ,H⟩ := degree_reverse_near.{u} j hpar hrev hρ
      refine ⟨δ,hδ,?_⟩
      intro ε he hε G _ _ _ _ _ _ _ _ μ _ f hf
      dsimp only
      intro hJ₀ hJt hI hn
      rcases hn with ⟨h',_⟩ | ⟨_,hn⟩
      · exact (hfor h').elim
      · exact Hfinish G μ p q f (zero_lt_one.trans hrev.1) hpar.1 hf ⟨hJ₀,hJt⟩ hI
          (H ε he hε G μ f hf ⟨hJ₀,hJt⟩ hI hn)
    · refine ⟨1,zero_lt_one,?_⟩
      intro ε he hε G _ _ _ _ _ _ _ _ μ _ f hf
      dsimp only
      intro _ _ _ hn
      exact hn.elim (fun h => (hfor h.1).elim) (fun h => (hrev h.1).elim)

/-- The full degree-lowering theorem from the introduction, inequalities and stability. -/
theorem degree_lowering : DegreeLowering.{u} := ⟨degree_inequalities,degree_stability⟩

end LpGowers
