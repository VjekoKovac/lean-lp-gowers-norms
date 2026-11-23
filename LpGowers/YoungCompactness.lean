module

public import LpGowers.YoungAffineAction
public import LpGowers.SharpYoungEquality
public import LpGowers.YoungStrongContinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Sequential compactness and stability in sharp Young's inequality

For a normalized extremizing sequence, the compactness input asks for strong
convergence after passing to affine coordinates and a subsequence. Continuity,
classification and the uniform deficit then follow. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

/-- Normalized nonnegative diagonal Young extremizing sequences are relatively
compact in the critical Lebesgue space modulo translations and invertible linear maps. -/
def YoungAffinePrecompact (n : ℕ) : Prop :=
  ∀ s : ℝ, 1 < s → ∀ F : ℕ → Rn n → ℝ≥0,
    (∀ k, AEMeasurable (F k) (euclideanMeasure n)) →
    (∀ k, ∫⁻ x, (F k x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n = 1) →
    Tendsto (fun k => cubeMoment 1 n s (F k)) atTop (𝓝 (youngMomentConstant 1 n s)) →
    ∃ (φ : ℕ → ℕ) (A : ℕ → YoungAffine n) (g : Rn n → ℝ≥0), StrictMono φ ∧
      AEMeasurable g (euclideanMeasure n) ∧
      Tendsto (fun k => lpDist (euclideanMeasure n) (criticalExponent 1 s)
        ((A k).act (criticalExponent 1 s) (F (φ k))) g) atTop (𝓝 0)

private theorem mass_congr_ae {n : ℕ} {q : ℝ} {f g : Rn n → ℝ≥0}
    (e : f =ᵐ[euclideanMeasure n] g) :
    (∫⁻ x, (f x : ℝ≥0∞)^q ∂euclideanMeasure n) =
      ∫⁻ x, (g x : ℝ≥0∞)^q ∂euclideanMeasure n :=
  lintegral_congr_ae (e.mono fun x hx => by simp [hx])

private theorem distance_congr_right {n : ℕ} (q : ℝ) (f : Rn n → ℝ≥0)
    {g h : Rn n → ℝ≥0} (e : g =ᵐ[euclideanMeasure n] h) :
    lpDist (euclideanMeasure n) q f g = lpDist (euclideanMeasure n) q f h := by
  unfold lpDist lp
  congr 1
  exact lintegral_congr_ae (e.mono fun x hx => by simp [hx])

private theorem unit_moment_le {n : ℕ} (s : ℝ) (hs : 1 ≤ s) (F : Rn n → ℝ≥0)
    (hf : AEMeasurable F (euclideanMeasure n))
    (hm : ∫⁻ x, (F x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n = 1) :
    cubeMoment 1 n s F ≤ youngMomentConstant 1 n s := by
  have : (euclideanMeasure n).IsAddLeftInvariant := by change (volume : Measure (Rn n)).IsAddLeftInvariant; infer_instance
  have H := euclidean_iterated_young (sharp_diagonal_young n) 1 s hs _ hf.measurable_mk
  dsimp only at H
  rw [← mass_congr_ae hf.ae_eq_mk, hm, ENNReal.one_rpow, mul_one] at H
  simpa only [cubeMoment, youngMomentConstant, autocorrelation_congr_ae _ hf.ae_eq_mk 1] using H

private theorem approximated_subsequence {n : ℕ} (hc : YoungAffinePrecompact n)
    {s : ℝ} (hs : 1 < s) (F : ℕ → Rn n → ℝ≥0)
    (hf : ∀ k, AEMeasurable (F k) (euclideanMeasure n))
    (hm : ∀ k, ∫⁻ x, (F k x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n = 1)
    (he : Tendsto (fun k => cubeMoment 1 n s (F k)) atTop (𝓝 (youngMomentConstant 1 n s)))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (k : ℕ) (v : Rn n → ℝ≥0), IsEuclideanGaussian v ∧
      (∫⁻ x, (v x : ℝ≥0∞)^criticalExponent 1 s ∂euclideanMeasure n) = 1 ∧
      lpDist (euclideanMeasure n) (criticalExponent 1 s) (F k) v ≤ ENNReal.ofReal τ := by
  let q := criticalExponent 1 s
  let μ := euclideanMeasure n
  have hqu : 1 ≤ q := by
    simp only [q, criticalExponent, Nat.cast_one, pow_one]
    exact (le_div_iff₀ (show 0 < 1+s by linarith)).2 (by linarith)
  have hq := zero_lt_one.trans_le hqu
  obtain ⟨φ,A,g,hφ,hg,hD⟩ := hc s hs F hf hm he
  let U k := (A k).act q (F (φ k))
  have hU k : AEMeasurable (U k) μ := (A k).aemeasurable (hf _) _
  have hUm k : ∫⁻ x, (U k x : ℝ≥0∞)^q ∂μ = 1 := ((A k).mass_act _ hq).trans (hm _)
  have hgm := unit_mass_of_lpDist_tendsto μ hqu hU hg hUm hD
  have hJ := youngMoment_tendsto_of_lpDist n hs hU hg hUm hD
  have hK : Tendsto (fun k => cubeMoment 1 n s (U k)) atTop (𝓝 (youngMomentConstant 1 n s)) := by
    simpa only [Function.comp_def, U, q, YoungAffine.moment_act _ (zero_lt_one.trans hs) (hf _)] using
      (he.comp hφ.tendsto_atTop)
  obtain ⟨V,hV,eg⟩ := sharpYoungEquality n s hs g hg hgm (tendsto_nhds_unique hK hJ).le
  obtain ⟨k,hk⟩ := (hD.eventually_lt_const (ENNReal.ofReal_pos.mpr hτ)).exists
  obtain ⟨v,hv,ev⟩ := (A k).pullback_gaussian (q:=q) hV
  refine ⟨φ k,v,hv,?_,?_⟩
  · rw [← (A k).mass_act v hq, ev, ← mass_congr_ae eg]
    exact hgm
  · rw [← (A k).distance_act _ _ hq, ev, ← distance_congr_right q _ eg]
    exact hk.le

/-- Compactness of extremizing sequences implies the uniform normalized inverse
theorem, with zero deficit allowed exactly at tolerance zero. -/
theorem sharpYoungInverse_of_affinePrecompact {n : ℕ} (hc : YoungAffinePrecompact n) :
    SharpYoungInverse n := by
  classical
  intro s hs τ hτ
  let q := criticalExponent 1 s
  let μ := euclideanMeasure n
  let C := youngMomentConstant 1 n s
  have hq : 0 < q := by dsimp [q, criticalExponent]; positivity
  obtain hzero | hpos := hτ.eq_or_lt
  · subst τ
    refine ⟨0,le_rfl,zero_lt_one,fun h => h,fun _ => rfl,?_⟩
    intro F hf hm hnear
    obtain ⟨V,hV,eg⟩ := sharpYoungEquality n s hs F hf hm (by simpa using hnear)
    refine ⟨V,hV,(mass_congr_ae eg).symm.trans hm,?_⟩
    rw [← distance_congr_right q _ eg]
    simp [lpDist, lp, hq, q]
  by_contra! hn
  let a (k : ℕ) : ℝ := (1 / ((k:ℝ)+1))/2
  have ha k : 0 < a k := by dsimp [a]; positivity
  have hl k : a k < 1 := by
    dsimp [a]
    have h : 1 / ((k:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) k])
    linarith
  have bad k := hn (a k) (ha k).le (hl k) (fun _ => ha k) (fun h => (hpos.ne' h).elim)
  choose F hf hm hnear hbad using bad
  have hlim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).div_const 2
  have lim1 : Tendsto (fun k => ENNReal.ofReal (1-a k)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x:=(1:ℝ))).sub hlim)
  have limC : Tendsto (fun k => ENNReal.ofReal (1-a k)*C) atTop (𝓝 C) := by
    simpa using (ENNReal.Tendsto.mul_const (b:=C) lim1 (Or.inl one_ne_zero))
  have he := tendsto_of_tendsto_of_tendsto_of_le_of_le limC tendsto_const_nhds hnear
    (fun k => unit_moment_le s hs.le (F k) (hf k) (hm k))
  obtain ⟨k,v,hv,vm,hd⟩ := approximated_subsequence hc hs F hf hm he hpos
  exact (hbad k v hv vm).not_ge hd

/-- The full Euclidean introduction theorem follows from affine precompactness
of normalized diagonal Young extremizing sequences in positive dimensions. -/
theorem euclideanTheorem_of_affinePrecompact
    (hc : ∀ n : ℕ, 1 ≤ n → YoungAffinePrecompact n) : EuclideanTheorem :=
  euclideanTheorem_of_sharpYoung_and_inverse (fun n _ => sharp_diagonal_young n)
    (fun n hn => sharpYoungInverse_of_affinePrecompact (hc n hn))

end LpGowers
