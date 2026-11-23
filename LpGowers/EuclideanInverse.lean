module

public import LpGowers.EuclideanYoung
public import LpGowers.EuclideanAffine
public import LpGowers.PowerTransfer
public import LpGowers.Normalization
import LpGowers.DegreeProofs
import LpGowers.Nonvanishing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

/-! # Reduction to rigidity and stability in the last sharp Young step

The last Young exponent is strictly larger than one even when the original
exponent is one. We use the nonnegative diagonal specialization of the
classical classification of equality in sharp Young, and of Michael
Christ's *Near-extremizers of Young's inequality for Euclidean groups*
(Theorem 1.1, 2019). Both are explicit hypotheses.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal ENNReal
namespace LpGowers
noncomputable section

def cubeMoment (d n : ℕ) (p : ℝ) (f : Rn n → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ h, autocorrelation (euclideanMeasure n) d f h ^ p ∂cubeMeasure (euclideanMeasure n) d

def youngMomentConstant (d n : ℕ) (p : ℝ) : ℝ≥0∞ := ENNReal.ofReal (iteratedYoungFactor d p) ^ n


/-- In the inverse input the degree-one moment is exactly the autocorrelation
convolution norm to the power `s`, as in Christ's theorem. -/
theorem cubeMoment_one (n : ℕ) (s : ℝ) (F : Rn n → ℝ≥0)
    (hF : AEMeasurable F (euclideanMeasure n)) :
    let μ := euclideanMeasure n
    cubeMoment 1 n s F = ∫⁻ t, (∫⁻ x, (F x : ℝ≥0∞) * F (x+t) ∂μ)^s ∂μ := by
  let μ := euclideanMeasure n
  have : SigmaFinite μ := by unfold μ euclideanMeasure; infer_instance
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  let e := MeasurableEquiv.funUnique (Fin 1) (Rn n)
  have he : MeasurePreserving e (cubeMeasure μ 1) μ := measurePreserving_funUnique μ (Fin 1)
  have hm := (measurable_autocorrelation_of_aemeasurable μ 1 hF).pow_const s
  unfold cubeMoment
  calc
    _ = ∫⁻ t, autocorrelation μ 1 F (e.symm t) ^ s ∂μ :=
      ((MeasurePreserving.symm e he).lintegral_comp hm).symm
    _ = _ := by rfl

/-- The sharp bound for the degree-one moment is precisely the diagonal
Young factor from Section 4. -/
theorem youngMomentConstant_one (n : ℕ) (s : ℝ) :
    youngMomentConstant 1 n s = ENNReal.ofReal (diagonalYoungFactor s)^n := by
  simp [youngMomentConstant,iteratedYoungFactor,diagonalYoungFactor]

/-- Equality and near equality for the single diagonal sharp Young inequality.
Zero tolerance includes the classical exact equality statement. The function
`cubeMoment 1 n s F` is the `s`th power of the convolution norm, and the
factor is its sharp bound at unit input norm. -/
def SharpYoungInverse (n : ℕ) : Prop :=
  ∀ s : ℝ, 1 < s → ∀ τ : ℝ, 0 ≤ τ → ∃ α : ℝ,
    0 ≤ α ∧ α < 1 ∧ (0 < τ → 0 < α) ∧ (τ = 0 → α = 0) ∧
    ∀ F : Rn n → ℝ≥0, AEMeasurable F (euclideanMeasure n) →
      (∫⁻ x, (F x : ℝ≥0∞)^(criticalExponent 1 s) ∂euclideanMeasure n) = 1 →
      ENNReal.ofReal (1-α) * youngMomentConstant 1 n s ≤ cubeMoment 1 n s F →
      ∃ V : Rn n → ℝ≥0, IsEuclideanGaussian V ∧
        (∫⁻ x, (V x : ℝ≥0∞)^(criticalExponent 1 s) ∂euclideanMeasure n) = 1 ∧
        lpDist (euclideanMeasure n) (criticalExponent 1 s) F V ≤ ENNReal.ofReal τ

def lastYoungPower (k : ℕ) (p : ℝ) : ℝ := (2 : ℝ)^k * p / (p+k)

theorem lastYoungPower_critical (k : ℕ) (p : ℝ) (hp : 0 < p) :
    lastYoungPower k p * criticalExponent 1 (p+k) = criticalExponent (k+1) p := by
  unfold lastYoungPower criticalExponent
  push_cast; rw [pow_succ]
  field_simp; ring

private theorem cubeMoment_congr {n d : ℕ} {p : ℝ} {f g : Rn n → ℝ≥0}
    (h : f =ᵐ[euclideanMeasure n] g) : cubeMoment d n p f = cubeMoment d n p g := by
  let μ := euclideanMeasure n
  have : μ.IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  exact congrArg (fun R => ∫⁻ h, R h ^ p ∂cubeMeasure μ d) (autocorrelation_congr_ae μ h d)

/-- Any relative lower bound at degree `k+1` survives in the final, degree-one
Young step at exponent `p+k`. This includes exact equality (`C = 1`). -/
theorem lower_bound_last_Young {n : ℕ} (hY : SharpDiagonalYoung n) (k : ℕ)
    (p : ℝ) (hp : 1 ≤ p) (f : Rn n → ℝ≥0) (hf : AEMeasurable f (euclideanMeasure n))
    (C : ℝ≥0∞) (h : C * youngMomentConstant (k+1) n p ≤ cubeMoment (k+1) n p f) :
    C * youngMomentConstant 1 n (p+k) ≤
      cubeMoment 1 n (p+k) (fun x => f x ^ lastYoungPower k p) := by
  induction k generalizing p f with
  | zero =>
      have hp' := lt_of_lt_of_le zero_lt_one hp
      simpa [lastYoungPower, hp'.ne'] using h
  | succ k ih =>
      have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have hA : 0 < diagonalYoungFactor p := by unfold diagonalYoungFactor; positivity
      let r := 2*p/(p+1)
      let F := hf.mk f
      have hF := hf.ae_eq_mk
      have mF := hf.measurable_mk
      have hrec := euclidean_young_recurrence hY (k+1) p hp F mF
      change cubeMoment (k+1+1) n p F ≤ _ * cubeMoment (k+1) n (p+1) (fun x => F x ^ r) at hrec
      rw [← cubeMoment_congr hF] at hrec
      have hr : 0 ≤ r := by unfold r; positivity
      have hFg : (fun x => F x ^ r) =ᵐ[euclideanMeasure n] (fun x => f x ^ r) :=
        hF.symm.fun_comp (fun a => a ^ r)
      rw [cubeMoment_congr hFg] at hrec
      have fact : youngMomentConstant (k+1+1) n p =
          (ENNReal.ofReal (diagonalYoungFactor p))^n * youngMomentConstant (k+1) n (p+1) := by
        unfold youngMomentConstant
        rw [← youngFactor_rec (k+1) p hp', ENNReal.ofReal_mul hA.le, mul_pow]
      have H := h.trans hrec
      rw [fact, mul_left_comm] at H
      have hnext := (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hA))
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp H
      have hfinal := ih (p+1) (by linarith) (fun x => f x ^ r) (hf.pow_const r) hnext
      have hs : p+1+(k : ℝ) = p+(k+1 : ℕ) := by push_cast; ring
      have he : r * lastYoungPower k (p+1) = lastYoungPower (k+1) p := by
        unfold r lastYoungPower
        rw [hs, pow_succ]
        field_simp
      simpa only [hs, ← NNReal.rpow_mul, he] using hfinal

lemma gaussian_power {n : ℕ} {g : Rn n → ℝ≥0} (hg : IsEuclideanGaussian g)
    {γ : ℝ} (hγ : 0 < γ) : IsEuclideanGaussian (fun x => g x ^ γ) := by
  obtain ⟨c,x₀,M,hc,hs,hM,hg⟩ := hg
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => γ * M i j
  have hQ (v : Rn n) : gaussianQuad A v = γ * gaussianQuad M v := by
    simp [A, gaussianQuad, Finset.mul_sum, mul_left_comm, mul_assoc]
  refine ⟨c^γ,x₀,A,Real.rpow_pos_of_pos hc _,fun i j => by simp only [A,hs i j],
    fun v hv => (hQ v).symm ▸ mul_pos hγ (hM v hv), ?_⟩
  intro x
  rw [NNReal.coe_rpow, hg, Real.mul_rpow hc.le (Real.exp_nonneg _), ← Real.exp_mul, hQ]
  congr 2
  ring

private lemma gaussian_amplitude {n : ℕ} {g : Rn n → ℝ≥0} (hg : IsEuclideanGaussian g)
    {a : ℝ≥0} (ha : 0 < a) : IsEuclideanGaussian (fun x => a * g x) := by
  obtain ⟨c,x₀,M,hc,hs,hM,hg⟩ := hg
  refine ⟨(a:ℝ)*c,x₀,M,mul_pos ha hc,hs,hM,?_⟩
  intro x
  rw [NNReal.coe_mul, hg, mul_assoc]

private lemma gaussian_measurable {n : ℕ} {g : Rn n → ℝ≥0} (hg : IsEuclideanGaussian g) :
    Measurable g := by
  obtain ⟨c,x₀,M,_,_,_,hg⟩ := hg
  have he : g = fun x => (c * Real.exp (-gaussianQuad M (x-x₀))).toNNReal := by
    funext x; rw [← hg, Real.toNNReal_coe]
  rw [he]
  unfold gaussianQuad
  fun_prop

private lemma ae_eq_of_lpDist_zero {n : ℕ} {f g : Rn n → ℝ≥0} {q : ℝ} (hq : 0 < q)
    (hf : AEMeasurable f (euclideanMeasure n)) (hg : AEMeasurable g (euclideanMeasure n))
    (hh : lpDist (euclideanMeasure n) q f g = 0) : f =ᵐ[euclideanMeasure n] g := by
  have H := (lp_eq_zero_iff _ (hf.edist hg) hq).mp hh
  filter_upwards [H] with x hx
  exact edist_eq_zero.mp hx

private lemma transfer_with_zero {n : ℕ} {r γ η : ℝ} (hr : 0 < r) (hγ : 0 < γ) (hη : 0 ≤ η) :
    ∃ τ : ℝ, 0 ≤ τ ∧ (0 < η → 0 < τ) ∧
      ∀ U V : Rn n → ℝ≥0, AEMeasurable U (euclideanMeasure n) → AEMeasurable V (euclideanMeasure n) →
      (∫⁻ x, (U x : ℝ≥0∞)^r ∂euclideanMeasure n) = 1 →
      (∫⁻ x, (V x : ℝ≥0∞)^r ∂euclideanMeasure n) = 1 →
      lpDist (euclideanMeasure n) r U V ≤ ENNReal.ofReal τ →
      lpDist (euclideanMeasure n) (r/γ) (fun x => (U x)^γ) (fun x => (V x)^γ) ≤
        ENNReal.ofReal η := by
  rcases hη.eq_or_lt with h | h
  · subst η
    refine ⟨0, le_rfl, id, ?_⟩
    intro U V hU hV _ _ hh
    have H := ae_eq_of_lpDist_zero hr hU hV (le_zero_iff.mp (by simpa using hh))
    have e : (fun x => edist (U x ^ γ) (V x ^ γ) ^ (r/γ)) =ᵐ[euclideanMeasure n] 0 := by
      filter_upwards [H] with x hx
      simp [hx, ENNReal.zero_rpow_of_pos (div_pos hr hγ)]
    simp [lpDist,lp,lintegral_congr_ae e,div_pos hγ hr]
  · obtain ⟨τ,hτ,H⟩ := power_transfer_tolerance.{0} hr hγ h
    exact ⟨τ,hτ.le,fun _ => hτ,H _ _⟩

/-- Given sharp Young and its inverse, this is the desired conclusion for
unit inputs; `η=0` yields the equality classification with zero error. -/
theorem euclidean_inverse_unit {n : ℕ} (hY : SharpDiagonalYoung n) (hInv : SharpYoungInverse n)
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) (η : ℝ) (hη : 0 ≤ η) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ (0 < η → 0 < β) ∧ ∀ f : Rn n → ℝ≥0,
      AEMeasurable f (euclideanMeasure n) →
      (∫⁻ x, (f x : ℝ≥0∞)^(criticalExponent d p) ∂euclideanMeasure n) = 1 →
      ENNReal.ofReal (1-β) * ENNReal.ofReal (sharpEuclideanConstant d n p) ≤
        gowers (euclideanMeasure n) d p f →
      ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧
        (∫⁻ x, (g x : ℝ≥0∞)^(criticalExponent d p) ∂euclideanMeasure n) = 1 ∧
        lpDist (euclideanMeasure n) (criticalExponent d p) f g ≤ ENNReal.ofReal η := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let μ := euclideanMeasure n
  let s : ℝ := p+k
  let t := lastYoungPower k p
  let γ := 1/t
  let r := criticalExponent 1 s
  let q := criticalExponent (k+1) p
  let b := p * (2 : ℝ)^(k+1)
  have hp' := lt_of_lt_of_le zero_lt_one hp
  have hs : 1 < s := by
    have hk : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    dsimp [s]; linarith
  have ht : 0 < t := by dsimp [t,lastYoungPower]; positivity
  have hr : 0 < r := by have := lt_trans zero_lt_one hs; dsimp [r,criticalExponent]; positivity
  have hγ : 0 < γ := one_div_pos.mpr ht
  have hb : 0 < b := by dsimp [b]; positivity
  have htr : t*r=q := lastYoungPower_critical k p hp'
  have hrγ : r/γ=q := by simpa [γ,div_eq_mul_inv,mul_comm] using htr
  obtain ⟨τ,hτ,hτpos,htrn⟩ := transfer_with_zero (n := n) hr hγ hη
  obtain ⟨α,hα,hα1,hαpos,_,hinv⟩ := hInv s hs τ hτ
  let β := 1-(1-α)^(1/b)
  have hA : 0 < 1-α := by linarith
  have hB : 0 ≤ β := sub_nonneg.mpr (Real.rpow_le_one hA.le (by linarith) (by positivity))
  have hB1 : β < 1 := by dsimp [β]; linarith [Real.rpow_pos_of_pos hA (1/b)]
  refine ⟨β,hB,hB1,fun h => sub_pos.mpr (Real.rpow_lt_one hA.le
    (by linarith [hαpos (hτpos h)]) (by positivity)), ?_⟩
  intro f hf hm hnear
  let U := fun x => f x ^ t
  have hU : AEMeasurable U μ := hf.pow_const t
  have hUm : (∫⁻ x, (U x : ℝ≥0∞)^r ∂μ) = 1 := by
    simpa only [U, ENNReal.coe_rpow_of_nonneg _ ht.le, ← ENNReal.rpow_mul, htr] using hm
  have hbet : (ENNReal.ofReal (1-β))^b = ENNReal.ofReal (1-α) := by
    have he : 1-β = (1-α)^(1/b) := by dsimp [β]; ring
    rw [he, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_pos_of_pos hA _).le hb.le,
       ← Real.rpow_mul hA.le, one_div_mul_cancel hb.ne', Real.rpow_one]
  have hex : (1/p * (1/(2:ℝ)^(k+1))) * b = 1 := by unfold b; field_simp
  have hK := iteratedFactor_root (k+1) n p hp'
  have hpow := ENNReal.rpow_le_rpow hnear hb.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hb.le, hbet, ← hK, ← ENNReal.rpow_mul, hex, ENNReal.rpow_one] at hpow
  have hG : gowers μ (k+1) p f ^ b = cubeMoment (k+1) n p f := by
    unfold gowers lp cubeMoment
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc, hex, ENNReal.rpow_one]
  rw [hG] at hpow
  have hlast := lower_bound_last_Young hY k p hp f hf _ hpow
  obtain ⟨V,hV,hVm,herr⟩ := hinv U hU hUm hlast
  let g := fun x => V x ^ γ
  have hgm : (∫⁻ x, (g x : ℝ≥0∞)^q ∂μ) = 1 := by
    have hgq : γ*q = r := by rw [← htr]; dsimp [γ]; field_simp
    simpa only [g, ENNReal.coe_rpow_of_nonneg _ hγ.le, ← ENNReal.rpow_mul, hgq] using hVm
  refine ⟨g,gaussian_power hV hγ,hgm,?_⟩
  have h := htrn U V hU (gaussian_measurable hV).aemeasurable hUm hVm herr
  rw [hrγ] at h
  change lpDist μ q f g ≤ _
  simpa [U, γ, ← NNReal.rpow_mul, ht.ne', g] using h

/-- The source relative-error conclusions in the original normalization,
from sharp Young and the exact and near-extremiser results for sharp Young. -/
theorem euclidean_inverse_finite {n : ℕ} (hY : SharpDiagonalYoung n) (hInv : SharpYoungInverse n)
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p) (η : ℝ) (hη : 0 ≤ η) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ (0 < η → 0 < β) ∧ ∀ f : Rn n → ℝ≥0,
      let μ := euclideanMeasure n
      let q := criticalExponent d p
      let N := lp μ q (liftNN f)
      AEMeasurable f μ → N < ⊤ → (¬ f =ᵐ[μ] 0) →
      ENNReal.ofReal (1-β) * ENNReal.ofReal (sharpEuclideanConstant d n p) * N ≤
        gowers μ d p f →
      ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ lp μ q (liftNN g) = N ∧
        lpDist μ q f g ≤ ENNReal.ofReal η * N := by
  obtain ⟨β,hβ,hβ1,hβpos,H⟩ := euclidean_inverse_unit hY hInv d hd p hp η hη
  refine ⟨β,hβ,hβ1,hβpos,?_⟩
  intro f μ q N hf hfin hn hnear
  have hp' := lt_of_lt_of_le zero_lt_one hp
  have hq : 0 < q := by dsimp [q,criticalExponent]; positivity
  obtain ⟨a,F,ha0,ha,hF,hm,hamp⟩ := exists_unit_amplitude μ q hq f hf hn hfin
  change (a : ℝ≥0∞) = N at ha
  have hnear' := hnear
  rw [← hamp, gowers_smul_input μ a d F hp'] at hnear'
  change _ * N ≤ (a : ℝ≥0∞) * gowers μ d p F at hnear'
  rw [← ha, mul_comm _ (a : ℝ≥0∞)] at hnear'
  have hlow := (ENNReal.mul_le_mul_iff_right (by exact_mod_cast ha0.ne') ENNReal.coe_ne_top).mp hnear'
  obtain ⟨g,hg,hgm,hdist⟩ := H F hF hm hlow
  change (∫⁻ x, (g x : ℝ≥0∞)^q ∂μ) = 1 at hgm
  refine ⟨fun x => a * g x,gaussian_amplitude hg ha0,?_,?_⟩
  · rw [lp_smul_liftNN μ a g q hq]
    have hgN : lp μ q (liftNN g) = 1 := by simp only [lp,liftNN,hgm,ENNReal.one_rpow]
    rw [hgN,mul_one,ha]
  · rw [← hamp, lpDist_smul_input μ a F g hq, ← ha, mul_comm (ENNReal.ofReal η)]
    exact mul_le_mul_right hdist _

/-- Full Theorem 1.3 from the precise two external Euclidean inputs in §4.
The Gaussian tests, optimality, change of variables, Young iteration,
equality descent, near-equality descent, and power transfer are all proved. -/
theorem euclideanTheorem_of_sharpYoung_and_inverse
    (hY : ∀ n : ℕ, 1 ≤ n → SharpDiagonalYoung n)
    (hInv : ∀ n : ℕ, 1 ≤ n → SharpYoungInverse n) : EuclideanTheorem := by
  intro d n p hd hn hp μ q K
  have hp' := lt_of_lt_of_le zero_lt_one hp
  have hq : 0 < q := by dsimp [q,criticalExponent]; positivity
  refine ⟨euclideanBound_of_sharpDiagonalYoung (hY n hn) d p hp,
    euclideanConstant_le_of_bound d n p hp', ?_, ?_⟩
  · intro f hf hfin hnonzero
    refine ⟨?_, ae_gaussian_equality d p hp' f⟩
    intro he
    obtain ⟨β,hβ,_,_,H⟩ := euclidean_inverse_finite (hY n hn) (hInv n hn) d hd p hp 0 le_rfl
    have hcoef : ENNReal.ofReal (1-β) ≤ 1 := by exact_mod_cast (ENNReal.ofReal_le_one.mpr (by linarith))
    have hlow : ENNReal.ofReal (1-β)*K*lp μ q (liftNN f) ≤ gowers μ d p f := by
      rw [he]
      calc
        _ ≤ 1 * K * lp μ q (liftNN f) := by gcongr
        _ = _ := by simp
    obtain ⟨g,hg,_,hdist⟩ := H f hf hfin hnonzero hlow
    exact ⟨g,hg,ae_eq_of_lpDist_zero hq hf (gaussian_measurable hg).aemeasurable
      (le_zero_iff.mp (by simpa using hdist))⟩
  · intro η hη
    obtain ⟨β,_,_,hβpos,H⟩ := euclidean_inverse_finite (hY n hn) (hInv n hn) d hd p hp η hη.le
    refine ⟨β,hβpos hη,?_⟩
    intro ε _ hε f hf hfin hnonzero hnear
    apply H f hf hfin hnonzero
    refine le_trans ?_ hnear
    gcongr

/-- The exact, normalized equality classification in the diagonal sharp Young
inequality. No approximation statement is included in this hypothesis. -/
def SharpYoungEquality (n : ℕ) : Prop :=
  ∀ s : ℝ, 1 < s → ∀ F : Rn n → ℝ≥0, AEMeasurable F (euclideanMeasure n) →
    (∫⁻ x, (F x : ℝ≥0∞)^(criticalExponent 1 s) ∂euclideanMeasure n) = 1 →
    youngMomentConstant 1 n s ≤ cubeMoment 1 n s F →
    ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ F =ᵐ[euclideanMeasure n] g

/-- Exact equality descends to the last Young step on its own, including
the endpoint p=1 and every nonzero input of finite critical norm. -/
theorem euclidean_equality_of_young_equality {n : ℕ} (hY : SharpDiagonalYoung n)
    (hEq : SharpYoungEquality n) (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1 ≤ p)
    (f : Rn n → ℝ≥0) (hf : AEMeasurable f (euclideanMeasure n))
    (hfin : lp (euclideanMeasure n) (criticalExponent d p) (liftNN f) < ⊤)
    (hne : ¬ f =ᵐ[euclideanMeasure n] 0) :
    (gowers (euclideanMeasure n) d p f = ENNReal.ofReal (sharpEuclideanConstant d n p) *
       lp (euclideanMeasure n) (criticalExponent d p) (liftNN f)) ↔
    ∃ g : Rn n → ℝ≥0, IsEuclideanGaussian g ∧ f =ᵐ[euclideanMeasure n] g := by
  have hp' := zero_lt_one.trans_le hp
  refine ⟨?_, ae_gaussian_equality d p hp' f⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  intro h
  let μ := euclideanMeasure n
  let q := criticalExponent (k+1) p
  let t := lastYoungPower k p
  let s : ℝ := p + k
  have hs : 1 < s := by
    have hk : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    dsimp [s]; linarith
  have hq : 0 < q := by dsimp [q,criticalExponent]; positivity
  have ht : 0 < t := by dsimp [t,lastYoungPower]; positivity
  obtain ⟨a,F,ha0,ha,hF,hm,hamp⟩ := exists_unit_amplitude μ q hq f hf hne hfin
  have hu : gowers μ (k+1) p F = ENNReal.ofReal (sharpEuclideanConstant (k+1) n p) := by
    change gowers μ (k+1) p f = _ * lp μ q (liftNN f) at h
    rw [← ha, ← hamp, gowers_smul_input μ a (k+1) F hp', mul_comm _ (a : ℝ≥0∞)] at h
    exact (ENNReal.mul_right_inj (by exact_mod_cast ha0.ne') ENNReal.coe_ne_top).mp h
  have hroot : (1/p * (1/(2:ℝ)^(k+1))) * (p * (2:ℝ)^(k+1)) = 1 := by field_simp
  have hmoment : cubeMoment (k+1) n p F = youngMomentConstant (k+1) n p := by
    rw [← iteratedFactor_root (k+1) n p hp'] at hu
    have hh := congrArg (fun x : ℝ≥0∞ => x ^ (p * (2:ℝ)^(k+1))) hu
    simpa only [gowers, lp, ← ENNReal.rpow_mul, ← mul_assoc, hroot,
      ENNReal.rpow_one, μ, cubeMoment, youngMomentConstant] using hh
  have hlast := lower_bound_last_Young hY k p hp F hF 1 (by simp [hmoment])
  have hunit : (∫⁻ x, ((F x ^ t : ℝ≥0) : ℝ≥0∞)^(criticalExponent 1 s) ∂μ) = 1 := by
    simpa only [ENNReal.coe_rpow_of_nonneg _ ht.le, ← ENNReal.rpow_mul,
      lastYoungPower_critical k p hp',t,s] using! hm
  obtain ⟨g,hg,he⟩ := hEq s hs _ (hF.pow_const t) hunit (by simpa using hlast)
  refine ⟨fun x => a * g x ^ (1/t),gaussian_amplitude (gaussian_power hg (one_div_pos.mpr ht)) ha0,?_⟩
  rw [← hamp]
  filter_upwards [he] with x hx
  simp only [← hx, ← NNReal.rpow_mul, mul_one_div_cancel ht.ne', NNReal.rpow_one]

end
end LpGowers
