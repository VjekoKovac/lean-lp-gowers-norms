module

public import LpGowers.DiscretePatternBound
public import LpGowers.DiscreteConcentratedPatterns
public import LpGowers.DiscreteEntropyRates
import Mathlib.Tactic

/-! # The diffuse part of the large-degree entropy estimate -/

@[expose] public section
noncomputable section
open Filter
open scoped NNReal BigOperators Topology
namespace LpGowers.Discrete

private theorem diffuse_zero (N p : ℕ) (hp : 1≤p) (g : ℤ → ℝ≥0) (t : ℝ) (ht : 0≤t)
    (β : ℝ≥0) (hg : ∀ i∈Finset.Ico 0 ((N+1:ℕ):ℤ), g i ≤ β) :
    ((∑ i ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g i^(t/p))^p : ℝ≥0) ≤ (N+1:ℕ)^p*β^t := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hh : ∑ i ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g i^(t/p) ≤ (N+1:ℕ)*β^(t/p) := by
    calc
      _ ≤ ∑ _i ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), β^(t/p) := Finset.sum_le_sum fun i hi =>
        NNReal.rpow_le_rpow (hg i hi) (div_nonneg ht hp'.le)
      _ = _ := by simp [Int.card_Ico]
  apply (pow_le_pow_left' hh p).trans
  rw [mul_pow, ← NNReal.rpow_natCast (_^(_ : ℝ)), ← NNReal.rpow_mul, div_mul_cancel₀ _ hp'.ne']

/-- For each fixed threshold β<1, the complete pattern sum is ≤1 uniformly
in all normalized g with all coordinates ≤β, eventually in d. -/
theorem diffuse_patterns_le_one (N p : ℕ) (hN : 1≤N) (hp : 1≤p) (δ : ℝ) (hδ : 0<δ)
    (β : ℝ≥0) (hβ : β<1) (hcard : (activePatterns (N+1) N).card ≤ 2^N) :
    ∀ᶠ d : ℕ in atTop, ∀ g : ℤ→ℝ≥0, (∑ j ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g j = 1) →
      (∀ i∈Finset.Ico 0 ((N+1:ℕ):ℤ), g i ≤ β) →
      patternUpperSum N p d g (largeDegreeMainTerm (N+1) d+δ) ≤ 1 := by
  let T (d : ℕ) := largeDegreeMainTerm (N+1) d + δ
  let J := (Finset.Icc 1 N).erase N
  let M (l : ℕ) : ℝ := (patternCoefficient N p l:ℝ) * (activePatterns (N+1) l).card
  let minor (l d : ℕ) : ℝ := M l * ((d:ℝ)^l * 2^(-binomialEntropy l * T d))
  let zeroCost (d : ℕ) := ((N+1:ℕ):ℝ)^p * (β:ℝ)^(T d)
  let cap := (2:ℝ)^(-binomialEntropy N*δ)
  have hcap : cap<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (binomialEntropy_pos hN)) hδ)
  have hT := entropyMainTerm_tendsto N hN δ
  have hminor (l : ℕ) (hl : l∈J) : Tendsto (minor l) atTop (𝓝 0) := by
    have hI := Finset.mem_Icc.mp (Finset.mem_erase.mp hl).2
    have hne := (Finset.mem_erase.mp hl).1
    simpa [minor] using (entropy_minor_rate N l hI.1 (lt_of_le_of_ne hI.2 hne) δ).const_mul (M l)
  have hz : Tendsto zeroCost atTop (𝓝 0) := by
    have h := (tendsto_rpow_atTop_of_base_lt_one (β:ℝ) (by linarith [β.coe_nonneg]) hβ).comp hT
    simpa [zeroCost,T] using h.const_mul (((N+1:ℕ):ℝ)^p)
  have hsum : Tendsto (fun d => zeroCost d + ∑ l ∈ J, minor l d) atTop (𝓝 0) := by
    simpa using hz.add (tendsto_finsetSum J hminor)
  have hs := hsum.eventually (gt_mem_nhds (show (0:ℝ)<1-cap by linarith))
  filter_upwards [hs,hT.eventually_ge_atTop 0,eventually_ge_atTop 1] with d hd ht hdpos
  intro g hg hgβ
  let E (l : ℕ) : ℝ≥0 := (d.choose l:ℝ≥0)*patternCoefficient N p l *
    ∑ z ∈ activePatterns (N+1) l, subsetMonomial l (patternPoint z) g (T d)
  have hE (l : ℕ) : (E l:ℝ) ≤ (d.choose l:ℝ) * M l * 2^(-binomialEntropy l * T d) := by
    dsimp [E,M]
    push_cast
    calc
      _ ≤ (d.choose l:ℝ) * (patternCoefficient N p l:ℝ) *
          ∑ _z ∈ activePatterns (N+1) l, 2^(-binomialEntropy l*T d) := by
            gcongr with z hz
            exact patternMonomial_entropy hz g hg _ ht
      _ = _ := by simp; ring
  have hminorE (l : ℕ) (_ : l∈J) : (E l:ℝ) ≤ minor l d := by
    refine (hE l).trans ?_
    dsimp [minor]
    rw [mul_comm _ (M l), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by dsimp [M]; positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_pow d l
  have hmajor : (E N:ℝ) ≤ cap := by
    apply (hE N).trans
    have hm : M N ≤ 2^N := by
      simpa [M,patternCoefficient] using (show ((activePatterns (N+1) N).card:ℝ) ≤ 2^N by exact_mod_cast hcard)
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (by positivity))
    exact entropy_leading_rate N d hN hdpos δ
  have hzero := diffuse_zero N p hp g (T d) ht β hgβ
  change _ + ∑ l ∈ Finset.Icc 1 N, E l ≤ _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨hN,le_rfl⟩)]
  have hme := Finset.sum_le_sum hminorE
  have hme' : ((∑ l ∈ J, E l : ℝ≥0):ℝ) ≤ ∑ l ∈ J, minor l d := by exact_mod_cast hme
  let z : ℝ≥0 := (∑ i ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g i^(T d/p))^p
  have hzero' : (z:ℝ) ≤ zeroCost d := by
    dsimp only [z,zeroCost]
    exact_mod_cast hzero
  change z + (∑ l ∈ J, E l + E N) ≤ _
  rw [← add_assoc]
  have he : (z:ℝ) + ((∑ l ∈ J, E l : ℝ≥0):ℝ) + (E N:ℝ) ≤ 1 := by
    change zeroCost d + ∑ l ∈ J, minor l d < 1-cap at hd
    linarith only [hzero', hme', hmajor, hd]
  exact_mod_cast he



/-- Uniform in all normalized nonnegative functions, the active pattern
bound is at most one for the trial exponent in the proof of Theorem 1.5(c). -/
theorem patternUpperSum_eventually (N p : ℕ) (hN : 1≤N) (hp : 1≤p) (δ : ℝ) (hδ : 0<δ)
    (hcard : (activePatterns (N+1) N).card ≤ 2^N) :
    ∀ᶠ d : ℕ in atTop, ∀ g : ℤ→ℝ≥0, (∑ j ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g j = 1) →
      patternUpperSum N p d g (largeDegreeMainTerm (N+1) d+δ) ≤ 1 := by
  let T (d : ℕ) := largeDegreeMainTerm (N+1) d + δ
  let C : ℝ≥0 := ∑ l ∈ Finset.Icc 1 N, patternCoefficient N p l*(activePatterns (N+1) l).card
  obtain ⟨θ,hθ₀,hθ,hrate⟩ := exists_entropy_threshold N hN δ
  have hβ : 1-θ < 1 := tsub_lt_self zero_lt_one hθ₀
  have hdif := diffuse_patterns_le_one N p hN hp δ hδ (1-θ) hβ hcard
  have hz := (hrate.const_mul (C:ℝ)).eventually (gt_mem_nhds (show (C:ℝ)*0<1 by simp))
  have hT := entropyMainTerm_tendsto N hN δ
  filter_upwards [hdif,hz,hT.eventually_ge_atTop (2*p),hT.eventually_ge_atTop (2^N),
    eventually_ge_atTop 1] with d hdif hz ht hN' hdpos
  intro g hg
  by_cases hsmall : ∀ i ∈ Finset.Ico 0 ((N+1:ℕ):ℤ), g i ≤ 1-θ
  · exact hdif g hg hsmall
  push Not at hsmall
  obtain ⟨i,hi,hgi⟩ := hsmall
  have hi' := small_outside_peak _ g hi hg hgi.le
  have hrate' : C*(d:ℝ≥0)^N * θ^(T d/2^N-1) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    push_cast
    exact (le_of_lt (by simpa [T,mul_assoc] using hz))
  have hzero : 2 ≤ T d/p := (le_div_iff₀ (by exact_mod_cast hp : (0:ℝ)<p)).mpr ht
  have hmin : 1 ≤ T d/2^N := (le_div_iff₀ (by positivity)).mpr (by simpa [T] using hN')
  exact concentrated_patterns_le_one (N+1) N d p hdpos hp g _ _ hθ₀ hθ.le hg i hi' hzero hmin hrate'

end LpGowers.Discrete
