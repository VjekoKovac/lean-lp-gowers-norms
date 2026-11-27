module

public import LpGowers.YoungGaussianUpdate
public import LpGowers.YoungRealEuler
public import LpGowers.YoungUnitInput
import Mathlib.Tactic

/-! Local sequential compactness for the actual sharp Young Euler map at
a spherical Gaussian. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LpGowers

/-- Near any prescribed centered scalar Gaussian, approximate fixed points
of the normalized Young update at s≥2 form a precompact sequence. -/
theorem euclidean_gaussian_youngEuler_precompact (n : ℕ) (s : ℝ) (hs : 2≤s)
    [Fact (1≤ENNReal.ofReal (2*s/(s+1)))] [Fact (1≤ENNReal.ofReal s)]
    [Fact (1≤ENNReal.ofReal (s/(s-1)))] [Fact (1≤ENNReal.ofReal (2*s/(s-1)))]
    (G : EuclideanLp n (2*s/(s+1))) (hG : IsYoungProfile G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℕ → EuclideanLp n (2*s/(s+1)), (∀ k, dist (u k) G < ε) →
      Tendsto (fun k => u k - youngRealEuler n s hs (u k)) atTop (𝓝 0) →
      ∃ g : EuclideanLp n (2*s/(s+1)), ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (u ∘ σ) atTop (𝓝 g) := by
  have hs' : 1<s := by linarith
  have hs0 := zero_lt_one.trans hs'
  have hs1 := sub_pos.mpr hs'
  have hp₁ : Real.HolderConjugate (2*s/(s-1)) (2*s/(s+1)) := by
    refine ⟨?_,by positivity,by positivity⟩
    field_simp
    ring
  have hp₂ : Real.HolderConjugate s (s/(s-1)) := by
    refine ⟨?_,hs0,by positivity⟩
    field_simp
    ring
  let := hp₁.ennrealOfReal
  let := hp₂.ennrealOfReal
  have ha : 1 < 2*s/(s-1)-1 := by
    have h : 2 < 2*s/(s-1) := (lt_div_iff₀ hs1).mpr (by linarith)
    linarith
  exact gaussian_youngUpdate_precompact ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top _ _ _ ha (by linarith : 1≤s-1)
    (young_outer_exponents hs') (young_inner_exponents hs')
    (diagonalCorrCLM n s hs') (adjointCorrCLM n s hs')
    (diagonalCorrCLM_ae n s hs') (adjointCorrCLM_ae n s hs') G hG

/-- Every unit Young extremizing sequence in a fixed neighborhood of a
spherical Gaussian has a strongly convergent subsequence. -/
theorem local_young_precompact (n : ℕ) (s : ℝ) (hs : 2≤s)
    (hq : 0<criticalExponent 1 s) [Fact (1≤ENNReal.ofReal (criticalExponent 1 s))]
    (G : YoungUnitInput n (criticalExponent 1 s)) (hG : IsYoungProfile (G.toLp hq)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℕ → YoungUnitInput n (criticalExponent 1 s),
      (∀ k, dist ((u k).toLp hq) (G.toLp hq) < ε) →
      Tendsto (fun k => cubeMoment 1 n s (u k).val) atTop (𝓝 (youngMomentConstant 1 n s)) →
      ∃ g : EuclideanLp n (criticalExponent 1 s), ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => (u (σ k)).toLp hq) atTop (𝓝 g) := by
  have he : criticalExponent 1 s = 2*s/(s+1) := by simp [criticalExponent,add_comm]
  revert hG G hq
  revert ‹Fact (1≤ENNReal.ofReal (criticalExponent 1 s))›
  rw [he]
  intro hinst hq G hG
  have hs1 : 1<s := by linarith
  have hs0 := zero_lt_one.trans hs1
  let : Fact (1≤ENNReal.ofReal s) := ⟨ENNReal.one_le_ofReal.mpr hs1.le⟩
  let : Fact (1≤ENNReal.ofReal (s/(s-1))) := ⟨ENNReal.one_le_ofReal.mpr
    ((le_div_iff₀ (sub_pos.mpr hs1)).2 (by linarith))⟩
  let : Fact (1≤ENNReal.ofReal (2*s/(s-1))) := ⟨ENNReal.one_le_ofReal.mpr
    ((le_div_iff₀ (sub_pos.mpr hs1)).2 (by linarith))⟩
  obtain ⟨ε,hε,comp⟩ := euclidean_gaussian_youngEuler_precompact n s hs (G.toLp hq) hG
  refine ⟨ε,hε,?_⟩
  intro u hclose hmoment
  apply comp (fun k => (u k).toLp hq) hclose
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [← dist_eq_norm]
  have hm k : (∫⁻ x, ((u k).val x : ℝ≥0∞)^(criticalExponent 1 s) ∂euclideanMeasure n) = 1 := by
    rw [he]
    exact (u k).mass
  exact tendsto_dist_youngRealEuler n s hs (fun k => (u k).toLp hq) (fun k => (u k).val)
    (fun k => (u k).meas) (fun k => (u k).toLp_coe hq) hm hmoment

end LpGowers
