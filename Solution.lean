module

public import LpGowers

/-! Proofs compared with the independently specified declarations in Challenge.lean. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Pointwise Topology Classical

namespace LpGowers

/-- The uniform strict improvement of ordinary Gowers log-convexity. -/
theorem theorem_1_1 : ImprovedLogConvexity := improved_log_convexity

/-- Theorem 1.2, the Lebesgue bound and uniform classification of near-extremisers. -/
theorem theorem_1_2 : LebesgueEstimate := lebesgueEstimate

/-- The complete sharp inequality, optimality and equality classification of Theorem 1.3(a). -/
theorem theorem_1_3a (d n : ℕ) (p : ℝ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    let μ := euclideanMeasure n
    let q := criticalExponent d p
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧
    (∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k) ∧
    (∀ f : Rn n → ℝ≥0, AEMeasurable f μ →
      lp μ q (liftNN f) < ⊤ → (¬ f =ᵐ[μ] 0) →
      (gowers μ d p f = K * lp μ q (liftNN f) ↔
        ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[μ] g)) := by
  exact euclideanPartA d n p hd hn hp

/-- Theorem 1.4, including both degree-lowering inequalities and their stability statements. -/
theorem theorem_1_4 : DegreeLowering := degree_lowering

/-- The three discrete-cube estimates, including the additive fixed-side asymptotic. -/
theorem theorem_1_5 : Discrete.DiscreteClaim := Discrete.discreteClaim

end LpGowers

namespace LpGowers.Checked

theorem subgroupIndicator {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [SigmaFinite μ] (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (d : ℕ) {p : ℝ} (hp : 0 < p) :
    gowers μ d p ((H : Set G).indicator (fun _ => (1 : ℝ≥0))) =
      μ (H : Set G) ^ (((d : ℝ) + p) / ((2 : ℝ) ^ d * p)) := by
  exact gowers_subgroup_indicator μ H hH d hp

theorem marginal {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] {f : G → ℝ≥0}
    (hf : AEMeasurable f μ) (k : ℕ) (i : Fin (k + 1)) (h : Fin k → G) :
    (∫⁻ t, autocorrelation μ (k + 1) f (i.insertNth (α := fun _ => G) t h) ∂μ) =
       (autocorrelation μ k f h) ^ (2 : ℕ) := by
  exact autocorrelation_marginal μ hf k i h

theorem degreeOneExponent {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) (k : ℕ) (q θ : Fin (k + 1) → ℝ)
    (h : DegreeParameters k 1 q θ) (hθ : DegreeForward 1 θ) :
    gowers μ (k + 1) 1 f = lowerProduct μ k q θ f := by
  exact degree_forward_endpoint μ hf k q θ h hθ

theorem exactMoments {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hA : (∫⁻ x, F x ^ a ∂μ) = 1) (hB : (∫⁻ x, F x ^ b ∂μ) = 1)
    (hC : (∫⁻ x, F x ^ c ∂μ) = 1) :
    ∀ᵐ x ∂μ, F x = 0 ∨ F x = 1 := by
  exact three_moments_exact μ hF ha hab hbc hA hB hC

theorem scalarGaussianCorrelation (a : ℝ) (ha : 0 < a) (d : ℕ) (h : Fin d → ℝ) :
    autocorrelation volume d (fun x => (Real.exp (-a * x ^ 2)).toNNReal) h =
      ENNReal.ofReal (Real.exp (-(a * 2 ^ d) * ((∑ i, h i ^ 2) / 4))) *
      ENNReal.ofReal (Real.sqrt (Real.pi / (a * 2 ^ d))) := by
  exact autocorrelation_scalarGaussian a ha d h

theorem binaryEnergy (d k : ℕ) :
    Discrete.energy d (k + 1) ({0, 1} : Finset (Discrete.Lattice 1)) =
      2 ^ (k + 1) + 2 * d := by
  exact Discrete.binary_energy d k

theorem binaryLower (d k : ℕ) :
    Discrete.logTwo ((2 : ℝ) ^ (k + 1) + 2 * d) ≤ Discrete.criticalT d (k + 1) 2 := by
  exact Discrete.binary_criticalT_lower d k

theorem finiteInterpolation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F μ) {p a b θ : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (h : 1 / p = θ / a + (1 - θ) / b) :
    lp μ p F ≤ lp μ a F ^ θ * lp μ b F ^ (1 - θ) := by
  exact lp_interpolate μ hF hp ha hb hθ hθ' h

/-- The sharp upper bound from Theorem 1.3(a) and the least admissible constant. -/
theorem euclideanSharpEstimate (d n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧ ∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k := by
  exact euclidean_sharp_estimate d n p hp

theorem gaussianEquality (d n : ℕ) (p : ℝ) (hp : 0 < p) :
    let g := fun x : Rn n => ∏ i, (Real.exp (-Real.pi * x i ^ 2)).toNNReal
    gowers (euclideanMeasure n) d p g = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN g) := by
  exact gaussian_test_equality d n p hp

theorem euclideanNecessaryConstant (d n : ℕ) (p : ℝ) (hp : 0 < p)
    (K : ℝ≥0∞) (hK : EuclideanBound d n p K) :
    ENNReal.ofReal (sharpEuclideanConstant d n p) ≤ K := by
  exact euclideanConstant_le_of_bound d n p hp K hK

theorem largeSideLimit (d k : ℕ) :
    Filter.Tendsto (Discrete.criticalT d (k + 1)) Filter.atTop
      (𝓝 ((d + (k + 1) : ℕ) : ℝ)) := by
  exact Discrete.criticalT_tendsto_add d k

theorem lebesgueInequality.{u} : LebesgueBound.{u} := by
  exact lebesgueBound.{u}

theorem degreeInequalities.{u} : DegreeInequalities.{u} := by
  exact degree_inequalities

theorem ordinaryLogConvex {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] (μ : Measure G) [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {d : ℕ} (hd : 2 ≤ d) :
    ordinaryGowers μ d f ≤ ordinaryGowers μ (d - 1) f ^ logTheta d *
      ordinaryGowers μ (d + 1) f ^ (1 - logTheta d) := by
  exact gowers_log_convex μ hf hd

theorem allGaussianEquality {n : ℕ} (d : ℕ) (p : ℝ) (hp : 0 < p) (f : Rn n → ℝ≥0)
    (h : ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g) :
    gowers (euclideanMeasure n) d p f = ENNReal.ofReal (sharpEuclideanConstant d n p) *
      lp (euclideanMeasure n) (criticalExponent d p) (liftNN f) := by
  exact ae_gaussian_equality d p hp f h

theorem binarySetExponent : Discrete.criticalT 2 2 2 = 3 := by
  exact Discrete.binary_criticalT_two_two

theorem binaryEnergyAllDimensions (m d k : ℕ) :
    Discrete.energy d (k + 1) (Discrete.box m 2) = (2 ^ (k + 1) + 2 * d) ^ m := by
  exact Discrete.full_binary_box_energy m d k

theorem setAttainment (d k n : ℕ) (hn : 2 ≤ n) :
    IsLeast (Discrete.setExponents d (k + 1) n) (Discrete.criticalT d (k + 1) n) := by
  exact Discrete.criticalT_isLeast d k n hn

theorem functionAttainment (d k n : ℕ) (hn : 2 ≤ n) :
    IsGreatest (Discrete.functionExponents d (k + 1) n) (Discrete.criticalQ d (k + 1) n) := by
  exact Discrete.criticalQ_isGreatest d k n hn

theorem productUpper (d k n : ℕ) (hn : 2 ≤ n) :
    Discrete.criticalQ d (k + 1) n * Discrete.criticalT d (k + 1) n ≤
      (2 : ℝ) ^ d * (k + 1 : ℕ) := by
  exact Discrete.criticalQ_mul_criticalT_le d k n hn

theorem binaryLargeDegree (k : ℕ) :
    Filter.Tendsto (fun d : ℕ => Discrete.criticalT d (k + 1) 2 /
      Discrete.logTwo (2 * (d : ℝ))) Filter.atTop (𝓝 1) := by
  exact Discrete.binary_criticalT_log_ratio k

theorem nearThreeMoments {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ), 0 ≤ ε → ε < δ →
    ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ),
    Measurable F → (∀ x, 0 ≤ F x) →
    (∀ s ∈ ({a,b,c} : Set ℝ), Integrable (fun x => F x ^ s) μ ∧
      |(∫ x, F x ^ s ∂μ) - 1| ≤ ε) →
    let E := {x | 1/2 < F x}
    MeasurableSet E ∧ μ E < ⊤ ∧ |μ.real E - 1| ≤ η ∧
      ∀ t ∈ Set.Icc a c, Integrable (fun x => |F x - E.indicator 1 x| ^ t) μ ∧
        (∫ x, |F x - E.indicator 1 x| ^ t ∂μ) ≤ η := by
  exact three_moments_near ha hab hbc hη

theorem binaryBothExponents :
    Discrete.criticalT 2 2 2 = 3 ∧ Discrete.criticalQ 2 2 2 = 8 / 3 := by
  exact Discrete.binary_critical_two_two

/-- The full diagonal leakage inequality, Lemma 6.3 of the paper. -/
theorem diagonalLeakage {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [SigmaFinite μ]
    {f : G → ℝ≥0} (hf : AEMeasurable f μ) {A : Set G} (hA : NullMeasurableSet A μ) :
    (∫⁻ h, A.indicator (1 : G → ℝ≥0∞) (h 0 + h 1) * autocorrelation μ 2 f h ∂cubeMeasure μ 2) ≤
      (∫⁻ s in A, ∫⁻ x, liftNN f x * liftNN f (x + s) ∂μ ∂μ) ^ (1/2:ℝ) *
        lp μ 1 (liftNN f) * (ordinaryGowers μ 3 f)^2 := by
  exact diagonal_leakage_nullMeasurableSet μ hf hA

/-- Both optimal exponents in Theorem 1.5(a), for every degree and outer exponent in the source. -/
theorem binarySharp : Discrete.BinaryClaim := by
  exact Discrete.binaryClaim

/-- Both lattice exponents are attained, with the equality in equation (1.12). -/
theorem criticalExponents : Discrete.AttainmentClaim := by
  exact Discrete.attainment

/-- Both logarithmic estimates in Theorem 1.5(b), with one absolute upper-deficit constant. -/
theorem largeSideSharp : Discrete.LargeSideClaim := by
  exact Discrete.largeSideClaim

/-- The lower inequality in the additive entropy asymptotic of Theorem 1.5(c). -/
theorem largeDegreeLower (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, Discrete.largeDegreeMainTerm n d - η ≤ Discrete.criticalT d p n := by
  exact Discrete.entropy_largeDegree_lower n p hn hp hη

end LpGowers.Checked
