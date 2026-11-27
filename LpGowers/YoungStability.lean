module

public import LpGowers.YoungOrbitPath
public import LpGowers.YoungCompactness
public import LpGowers.YoungLocalEuler
import Mathlib.Tactic

/-! Qualitative stability of the diagonal sharp Young inequality in the
range needed by the higher Gowers functionals. A heat path would carry any
violating input through a fixed positive distance from the Gaussian orbit.
After affine normalization the crossing inputs are locally precompact, and
their sharp limit belongs to that same orbit. -/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

private theorem stabilizedYoungAt {n : ℕ} {s : ℝ} (hs : 1<s)
    (hq : 1≤criticalExponent 1 s) [Fact (1≤ENNReal.ofReal (criticalExponent 1 s))]
    (G : YoungUnitInput n (criticalExponent 1 s)) (hG : IsEuclideanGaussian G.val)
    (loc : ∃ ρ : ℝ, 0<ρ ∧ ∀ u : ℕ → YoungUnitInput n (criticalExponent 1 s),
      (∀ k, dist ((u k).toLp (zero_lt_one.trans_le hq)) (G.toLp (zero_lt_one.trans_le hq)) < ρ) →
      Tendsto (fun k => cubeMoment 1 n s (u k).val) atTop (𝓝 (youngMomentConstant 1 n s)) →
      ∃ g : EuclideanLp n (criticalExponent 1 s), ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => (u (σ k)).toLp (zero_lt_one.trans_le hq)) atTop (𝓝 g)) :
    SharpYoungInverseAt n s := by
  classical
  let q := criticalExponent 1 s
  let μ := euclideanMeasure n
  let K := youngMomentConstant 1 n s
  have hq0 : 0<q := zero_lt_one.trans_le hq
  let S := unitGaussianSet n q hq0
  intro τ hτ
  obtain hz|hp := hτ.eq_or_lt
  · subst τ
    refine ⟨0,le_rfl,zero_lt_one,fun h => h,fun _ => rfl,?_⟩
    intro F hf hm hnear
    obtain ⟨g,hg,he⟩ := sharpYoungEquality n s hs F hf hm (by simpa using hnear)
    refine ⟨g,hg,(mass_congr_ae he).symm.trans hm,?_⟩
    rw [← distance_congr_right q F he]
    simp [lpDist,lp,hq0,q] at *
  obtain ⟨ρ,hρ,compact⟩ := loc
  let ε := min (ρ/2) (τ/2)
  have hε : 0<ε := lt_min (by linarith) (by linarith)
  have hερ : ε<ρ := (min_le_left ..).trans_lt (by linarith)
  have hετ : ε≤τ := (min_le_right ..).trans (by linarith)
  by_contra! hn
  let a (k : ℕ) : ℝ := (1 / ((k:ℝ)+1))/2
  have ha (k) : 0 < a k := by dsimp [a]; positivity
  have ha1 (k) : a k < 1 := by
    have hh : 1/((k:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α:=ℝ) k])
    dsimp [a]; linarith
  have bad k := hn (a k) (ha k).le (ha1 k) (fun _ => ha k) (fun h => (hp.ne' h).elim)
  choose F hf hm hnear hbad using bad
  let U (k) : YoungUnitInput n q := ⟨F k,hf k,hm k⟩
  have hfar k : τ ≤ Metric.infDist ((U k).toLp hq0) S := by
    by_contra! h
    obtain ⟨z,⟨g,hg,rfl⟩,hd⟩ := (Metric.infDist_lt_iff (unitGaussianSet_nonempty n q hq0)).mp h
    have hh := hbad k g.val hg g.mass
    have hd' := ENNReal.ofReal_le_ofReal hd.le
    rw [← edist_dist, YoungUnitInput.edist_toLp] at hd'
    exact hh.not_ge hd'
  have cross k := crossing_unit_input hs hq (ha1 k) hε (U k) (hnear k) (hετ.trans (hfar k))
  choose H hHscore hHdist using cross
  have norm k := normalize_near_gaussian hq0 (H k) G hG ((hHdist k).trans_lt hερ)
  choose A hA using norm
  let V k := (H k).act (A k) hq0
  have hlim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).div_const 2
  have hlim1 : Tendsto (fun k => ENNReal.ofReal (1-a k)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x:=(1:ℝ))).sub hlim)
  have hlimK : Tendsto (fun k => ENNReal.ofReal (1-a k) * K) atTop (𝓝 K) := by
    simpa using (ENNReal.Tendsto.mul_const (b:=K) hlim1 (Or.inl one_ne_zero))
  have hJ : Tendsto (fun k => cubeMoment 1 n s (V k).val) atTop (𝓝 K) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlimK tendsto_const_nhds
    · intro k
      change _ ≤ cubeMoment 1 n s ((A k).act q (H k).val)
      rw [(A k).moment_act (zero_lt_one.trans hs) (H k).meas]; exact hHscore k
    · intro k
      exact unit_moment_le s hs.le (V k).val (V k).meas (V k).mass
  obtain ⟨u,σ,hσ,hlimu⟩ := compact V hA hJ
  obtain ⟨g,hg,he⟩ := YoungUnitInput.gaussian_of_strong_extremizing_limit hs hq0
    (fun k => V (σ k)) u hlimu (hJ.comp hσ.tendsto_atTop)
  obtain ⟨k,hk⟩ := ((Metric.tendsto_nhds.mp hlimu) ε hε).exists
  rw [← he] at hk
  exact (hHdist (σ k)).not_lt ((orbit_distance_le_transformed_dist hq0 (H (σ k)) g hg (A (σ k))).trans_lt hk)

/-- Gaussian stability for the normalized diagonal Young moment in the entire
range used in the last degree-lowering step of Theorem 1.3(b). -/
theorem diagonal_young_stability_above_two (n : ℕ) : YoungInverseAboveTwo n := by
  intro s hs
  have hs' : 1 < s := by linarith
  let q := criticalExponent 1 s
  have hq : 1 ≤ q := by
    simp only [q, criticalExponent, Nat.cast_one, pow_one]
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let : Fact (1 ≤ ENNReal.ofReal (criticalExponent 1 s)) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
  let G := heatGaussianInput n hq0 (t := 1) zero_lt_one
  have hG : IsEuclideanGaussian G.val := rootedHeatGaussian_isGaussian n hq0 zero_lt_one
  have hP : IsYoungProfile (G.toLp hq0) := by
    let c := GeometricBrascampLieb.heatNormalization (E := YoungHilbert n) 1
    have hc : 0 < c := Real.exp_pos _
    refine ⟨c ^ (1 / q), (4 * (1 : ℝ))⁻¹ / q, Real.rpow_pos_of_pos hc _, by positivity, ?_⟩
    apply (G.toLp_coe hq0).trans
    exact Filter.Eventually.of_forall (rootedHeatGaussian_formula n hq0 (t := 1) zero_lt_one)
  exact stabilizedYoungAt hs' hq G hG (local_young_precompact n s hs hq0 G hP)

/-- Parts (a) and (b) of the sharp Euclidean theorem, including all affine
Gaussians and a uniform stability threshold for every tolerance. -/
theorem euclideanTheorem : EuclideanTheorem :=
  euclideanTheorem_of_sharpYoung_and_inverse_ge_two (fun n _ => sharp_diagonal_young n)
    (fun n _ => diagonal_young_stability_above_two n)

end LpGowers
