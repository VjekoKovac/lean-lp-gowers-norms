module

public import LpGowers.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-! Centered spherical real Gaussian profiles are closed under the two
correlations and powers occurring in the diagonal Young Euler equation. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Topology ENNReal
namespace LpGowers

/-- A centered scalar Gaussian of amplitude c and exponent a on the product coordinates. -/
def youngProfile (n : ℕ) (c a : ℝ) (x : Rn n) : ℝ := c * Real.exp (-a * ∑ i, (x i)^2)

theorem youngProfile_pos (n : ℕ) {c : ℝ} (hc : 0<c) (a : ℝ) (x : Rn n) :
    0 < youngProfile n c a x := mul_pos hc (Real.exp_pos _)

theorem youngProfile_rpow (n : ℕ) {c : ℝ} (hc : 0<c) (a t : ℝ) (x : Rn n) :
    (youngProfile n c a x)^t = youngProfile n (c^t) (a*t) x := by
  rw [youngProfile,Real.mul_rpow hc.le (Real.exp_pos _).le,← Real.exp_mul,youngProfile]
  ring_nf

private lemma profile_integrable (n : ℕ) (c : ℝ) {a : ℝ} (ha : 0<a) :
    Integrable (youngProfile n c a) (euclideanMeasure n) := by
  apply Integrable.const_mul
  simpa only [← Real.exp_sum, ← Finset.mul_sum] using!
    (Integrable.fin_nat_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ t => Real.exp (-a*t^2)) (fun _ => integrable_exp_neg_mul_sq ha))

theorem youngProfile_memLp (n : ℕ) {c a : ℝ} (hc : 0<c) (ha : 0<a) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hpt : p ≠ ∞) : MemLp (youngProfile n c a) p (euclideanMeasure n) := by
  have hm : AEStronglyMeasurable (youngProfile n c a) (euclideanMeasure n) := by
    apply Continuous.aestronglyMeasurable
    unfold youngProfile; fun_prop
  apply (integrable_norm_rpow_iff hm hp hpt).mp
  simpa only [Real.norm_eq_abs, abs_of_pos (youngProfile_pos n hc a _),
    youngProfile_rpow n hc a p.toReal] using!
    profile_integrable n (c^p.toReal) (mul_pos ha (ENNReal.toReal_pos hp hpt))

theorem integral_youngProfile (n : ℕ) (c a : ℝ) :
    ∫ x, youngProfile n c a x ∂euclideanMeasure n = c * (Real.sqrt (Real.pi/a))^n := by
  unfold youngProfile
  rw [integral_const_mul]
  congr 1
  change (∫ x : Rn n, Real.exp (-a * ∑ i, x i ^ 2)) = _
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fin_nat_prod_volume_eq_prod (fun _ : Fin n => fun t : ℝ => Real.exp (-a*t^2))]
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,integral_gaussian]

/-- The integral formula includes its amplitude, so no normalization is lost
when passing from correlation to the nonlinear powers. -/
theorem youngProfile_correlation (n : ℕ) (A B : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (x : Rn n) :
    ∫ y, youngProfile n A a y * youngProfile n B b (y+x) ∂euclideanMeasure n =
      youngProfile n (A*B*(Real.sqrt (Real.pi/(a+b)))^n) (a*b/(a+b)) x := by
  let : (euclideanMeasure n).IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  have hsum : a+b ≠ 0 := (add_pos ha hb).ne'
  let z : Rn n := fun i => b/(a+b) * x i
  have he (y : Rn n) :
      -a*(∑ i,y i ^2) - b*(∑ i,(y i+x i)^2) =
      -(a*b/(a+b))*(∑ i,x i^2) - (a+b)*(∑ i,(y i+z i)^2) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib,z]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring
  have hf (y : Rn n) :
      youngProfile n A a y * youngProfile n B b (y+x) =
      (A*B*Real.exp (-(a*b/(a+b))*(∑ i,x i^2))) * youngProfile n 1 (a+b) (y+z) := by
    simp only [youngProfile,Pi.add_apply,one_mul]
    rw [mul_mul_mul_comm,← Real.exp_add]
    rw [show -a*(∑ i,y i^2) + -b*(∑ i,(y i+x i)^2) =
      -(a*b/(a+b))*(∑ i,x i^2) + -(a+b)*(∑ i,(y i+z i)^2) by linarith only [he y],Real.exp_add]
    ring
  simp_rw [hf]
  rw [integral_const_mul,integral_add_right_eq_self,integral_youngProfile]
  unfold youngProfile
  ring

/-- A.e. centered Gaussian form, independent of the Lebesgue exponent used
to represent an input in a power or a convolution operator. -/
def IsYoungProfile {n : ℕ} (f : Rn n → ℝ) : Prop :=
  ∃ c a : ℝ, 0<c ∧ 0<a ∧ f =ᵐ[euclideanMeasure n] youngProfile n c a

theorem IsYoungProfile.memLp {n : ℕ} {f : Rn n → ℝ} (hf : IsYoungProfile f)
    {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ∞) : MemLp f p (euclideanMeasure n) := by
  obtain ⟨c,a,hc,ha,h⟩ := hf
  exact (memLp_congr_ae h).mpr (youngProfile_memLp n hc ha hp hpt)

theorem IsYoungProfile.correlation {n : ℕ} {f g : Rn n → ℝ}
    (hf : IsYoungProfile f) (hg : IsYoungProfile g) :
    IsYoungProfile (fun x => ∫ y, f y * g (y+x) ∂euclideanMeasure n) := by
  let : (euclideanMeasure n).IsAddRightInvariant := by change (volume : Measure (Rn n)).IsAddRightInvariant; infer_instance
  obtain ⟨A,a,hA,ha,ef⟩ := hf
  obtain ⟨B,b,hB,hb,eg⟩ := hg
  refine ⟨A*B*(Real.sqrt (Real.pi/(a+b)))^n,a*b/(a+b),by positivity,by positivity,?_⟩
  filter_upwards [] with x
  rw [← youngProfile_correlation n A B ha hb x]
  apply integral_congr_ae
  have eg' : (fun y => g (y+x)) =ᵐ[euclideanMeasure n]
      (fun y => youngProfile n B b (y+x)) := by
    exact (measurePreserving_add_right (euclideanMeasure n) x).quasiMeasurePreserving.ae_eq_comp eg
  exact ef.mul eg'

end LpGowers
