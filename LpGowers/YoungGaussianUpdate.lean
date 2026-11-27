module

public import LpGowers.YoungWeightedCorrelation
public import LpGowers.YoungUpdateDerivative
public import LpGowers.YoungPowerMap
import Mathlib.Tactic

/-! Strong precompactness near a fixed centered Gaussian of approximate
solutions of the diagonal Young Euler equation, including the endpoint of
linear inner power. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LpGowers

private theorem profile_signedPower {n : ℕ} {f : Rn n → ℝ} (h : IsYoungProfile f)
    {g : ℝ} (hg : 1≤g) : IsYoungProfile (fun x => signedPower g (f x)) := by
  obtain ⟨c,a,hc,ha,he⟩ := h
  refine ⟨c^g,a*g,Real.rpow_pos_of_pos hc _,mul_pos ha (zero_lt_one.trans_le hg),?_⟩
  filter_upwards [he] with x hx
  rw [hx,signedPower_nonneg_value hg (youngProfile_pos n hc a x).le,youngProfile_rpow n hc]

private theorem profile_power_weight {n : ℕ} {f : Rn n → ℝ} (h : IsYoungProfile f)
    {g : ℝ} (hg : 1<g) : IsYoungProfile (fun x => g * |f x|^(g-1)) := by
  obtain ⟨c,a,hc,ha,he⟩ := h
  refine ⟨g*c^(g-1),a*(g-1),mul_pos (zero_lt_one.trans hg) (Real.rpow_pos_of_pos hc _),
    mul_pos ha (sub_pos.mpr hg),?_⟩
  filter_upwards [he] with x hx
  rw [hx,abs_of_pos (youngProfile_pos n hc a x),youngProfile_rpow n hc]
  simp only [youngProfile,mul_assoc]

/-- In the normalized Young update the inner power b=s−1 can equal 1 while
the outer power a=r′−1 must exceed 1. All hypotheses on A,B are their actual
correlation formulas. No compactness or differentiation is assumed. -/
theorem gaussian_youngUpdate_precompact {n : ℕ} {r s v w : ℝ≥0∞}
    [Fact (1≤r)] [Fact (1≤v)] [Fact (1≤w)] [Fact (1≤s)] [w.HolderConjugate r] [s.HolderConjugate v]
    (hr : r≠∞) (hs : s≠∞) (hv : v≠∞) (hw : w≠∞)
    (a b c : ℝ) (ha : 1<a) (hb : 1≤b) (haw : w=r*ENNReal.ofReal a) (hbs : s=v*ENNReal.ofReal b)
    (A : Lp ℝ r (euclideanMeasure n) →L[ℝ] Lp ℝ r (euclideanMeasure n) →L[ℝ] Lp ℝ s (euclideanMeasure n))
    (B : Lp ℝ v (euclideanMeasure n) →L[ℝ] Lp ℝ r (euclideanMeasure n) →L[ℝ] Lp ℝ w (euclideanMeasure n))
    (hA : ∀ f g, A f g =ᵐ[euclideanMeasure n] fun x => ∫ y, f y * g (y+x) ∂euclideanMeasure n)
    (hB : ∀ f g, B f g =ᵐ[euclideanMeasure n] fun x => ∫ y, f y * g (y+x) ∂euclideanMeasure n)
    (G : Lp ℝ r (euclideanMeasure n)) (hG : IsYoungProfile G) :
    let P := signedPowerLp (euclideanMeasure n) s v b hb hbs
    let Q := signedPowerLp (euclideanMeasure n) w r a ha.le haw
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℕ → Lp ℝ r (euclideanMeasure n), (∀ k, dist (u k) G < ε) →
      Tendsto (fun k => u k - youngUpdateMap c A B P Q (u k)) atTop (𝓝 0) →
      ∃ g : Lp ℝ r (euclideanMeasure n), ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (u ∘ σ) atTop (𝓝 g) := by
  intro P Q
  let U := P (A G G)
  let V := B U G
  have profile_of_eq {f g : Rn n → ℝ} (h : f =ᵐ[euclideanMeasure n] g) (hg : IsYoungProfile g) :
      IsYoungProfile f := by
    obtain ⟨c,a,hc,ha,he⟩ := hg
    exact ⟨c,a,hc,ha,h.trans he⟩
  have hmA : IsYoungProfile (A G G) := profile_of_eq (hA G G) (hG.correlation hG)
  have hmU : IsYoungProfile U := profile_of_eq (signedPowerLp_coe _ s v b hb hbs (A G G))
    (profile_signedPower hmA hb)
  have hmV : IsYoungProfile V := profile_of_eq (hB U G) (hmU.correlation hG)
  obtain ⟨P',hp,_⟩ := hasStrictFDerivAt_signedPowerLp _ s v b hb hbs hv (A G G)
  obtain ⟨Q',hq,hweight⟩ := hasStrictFDerivAt_signedPowerLp _ w r a ha.le haw hr V
  obtain ⟨h₁,h₂⟩ := compact_gaussian_correlation_branches (s := s) hr hw hs B hB Q' hweight
    (profile_power_weight hmV ha) G U hG hmU
  exact youngUpdate_local_precompact c A B P Q G hp hq h₁ h₂

end LpGowers
