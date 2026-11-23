module

public import LpGowers.YoungExtremalLift
public import LpGowers.HeatQuadratic
public import LpGowers.HeatApproximation
public import LpGowers.GaussianLogClosure
public import LpGowers.GaussianRigidity
public import LpGowers.SharpEuclidean
import Mathlib.Tactic

/-! # Classification of equality in sharp Euclidean Young and Gowers inequalities

An exact extremizer gives an extremal geometric Brascamp–Lieb datum. Every
positive-time smoothing of its repeated density has a quadratic logarithm.
Along a sequence of times these smooth densities converge to the original
density almost everywhere. Exponential-quadratic closure and integrability
give a Gaussian representative.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter GeometricBrascampLieb
open scoped ENNReal NNReal Topology
namespace LpGowers

/-- Every normalized exact extremizer of the diagonal sharp Young inequality on
Euclidean space agrees almost everywhere with a positive-definite Gaussian. -/
theorem sharpYoungEquality (n : ℕ) : SharpYoungEquality n := by
  intro s hs F hF hunit hnear
  let μ := euclideanMeasure n
  let q := criticalExponent 1 s
  have hq : 0<q := by dsimp [q, criticalExponent]; positivity
  obtain ⟨u,huF,hu,hu0,hum,hscore⟩ := affine_score_of_diagonal_extremal hs F hF hunit hnear
  let U := fun x : Rn n => u (WithLp.toLp 2 x)
  have hUm : 0 < ∫ y, u y := hum ▸ zero_lt_one
  have hUn : ∀ᵐ x ∂volume, 0 ≤ U x := Eventually.of_forall fun x => hu0 _
  have hUnz : ¬ U =ᵐ[volume] 0 := by
    intro hz
    have he : MeasurePreserving (WithLp.ofLp : YoungHilbert n → Rn n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
    have hh := he.quasiMeasurePreserving.ae_eq_comp hz
    have huz : u =ᵐ[volume] 0 := by
      filter_upwards [hh] with x hx
      exact hx
    have hm := integral_congr_ae huz
    exact one_ne_zero (by simpa only [Pi.zero_apply,integral_zero,hum] using hm)
  obtain ⟨t,ht,_,hae⟩ := exists_heatConvolution_subsequence_ae hu hu0
  let G := fun (k : ℕ) (x : Rn n) => heatConvolution u (t k) (WithLp.toLp 2 x)
  have hG k := heat_exp_quadratic_of_affine_score u hu hu0 hUm (ht k) (hscore _ (ht k))
  have hconv : ∀ᵐ x ∂volume, Tendsto (fun k => G k x) atTop (𝓝 (U x)) :=
    (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving.ae hae
  obtain ⟨a,b,P,hP,hexp⟩ := ae_exp_quadratic_limit G U hUn hUnz hG hconv
  let T (x : Rn n) := F x ^ q
  have hTU : ∀ᵐ x ∂μ, (T x : ℝ) = U x := by
    have h := (PiLp.volume_preserving_toLp (Fin n)).quasiMeasurePreserving.ae_eq_comp huF
    filter_upwards [h] with x hx
    simpa only [T, U, Function.comp_apply, youngFirstDensity, WithLp.ofLp_toLp, NNReal.coe_rpow] using hx.symm
  have hFin : (∫⁻ x, (T x : ℝ≥0∞)^(1 : ℝ) ∂μ) ≠ ⊤ := by
    simpa only [T,ENNReal.rpow_one,ENNReal.coe_rpow_of_nonneg _ hq.le] using
      (show (∫⁻ x, (F x : ℝ≥0∞)^q ∂μ) ≠ ⊤ from hunit ▸ ENNReal.one_ne_top)
  obtain ⟨g,hg,hTg⟩ := gaussian_of_ae_exponential_quadratic T a b P hP (by
    filter_upwards [hTU,hexp] with x hx hy
    exact hx.trans hy) zero_lt_one hFin
  refine ⟨fun x => g x ^ (1/q), gaussian_power hg (one_div_pos.mpr hq), ?_⟩
  filter_upwards [hTg] with x hx
  change F x ^ q = g x at hx
  rw [← hx, ← NNReal.rpow_mul, mul_one_div_cancel hq.ne', NNReal.rpow_one]

/-- The full equality characterization in Theorem 1.3(a), including its endpoint. -/
theorem euclidean_equality {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p)
    (f : Rn n → ℝ≥0) (hf : AEMeasurable f (euclideanMeasure n))
    (hfin : lp (euclideanMeasure n) (criticalExponent d p) (liftNN f) < ⊤)
    (hne : ¬ f =ᵐ[euclideanMeasure n] 0) :
    (gowers (euclideanMeasure n) d p f = ENNReal.ofReal (sharpEuclideanConstant d n p) *
       lp (euclideanMeasure n) (criticalExponent d p) (liftNN f)) ↔
    ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g :=
  euclidean_equality_of_young_equality (sharp_diagonal_young n) (sharpYoungEquality n) d hd p hp f hf hfin hne

/-- Theorem 1.3(a) of Kovač and Rogers, with the sharp constant, its optimality,
and the full equality classification for nonzero finite-norm functions. -/
theorem euclideanPartA (d n : ℕ) (p : ℝ) (hd : 2 ≤ d) (_hn : 1 ≤ n) (hp : 1 ≤ p) :
    let μ := euclideanMeasure n
    let q := criticalExponent d p
    let K := ENNReal.ofReal (sharpEuclideanConstant d n p)
    EuclideanBound d n p K ∧
      (∀ k : ℝ≥0∞, EuclideanBound d n p k → K ≤ k) ∧
      (∀ f : Rn n → ℝ≥0, AEMeasurable f μ → lp μ q (liftNN f) < ⊤ →
         (¬ f =ᵐ[μ] 0) → (gowers μ d p f = K * lp μ q (liftNN f) ↔
           ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[μ] g)) :=
  ⟨(euclidean_sharp_estimate d n p hp).1,(euclidean_sharp_estimate d n p hp).2,
    fun f hf hfin hne => euclidean_equality d hd p hp f hf hfin hne⟩

end LpGowers
