module

public import LpGowers.YoungUnitInput
public import LpGowers.YoungGaussianOrbit
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-! The orbit of unit Gaussians in real Lᵖ and its invariant distance. -/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

def unitGaussianSet (n : ℕ) (q : ℝ) (hq : 0 < q) : Set (EuclideanLp n q) :=
  {z | ∃ g : YoungUnitInput n q, IsEuclideanGaussian g.val ∧ g.toLp hq = z}

def heatGaussianInput (n : ℕ) {q t : ℝ} (hq : 0<q) (ht : 0<t) : YoungUnitInput n q where
  val := rootedHeatGaussian n q t
  meas := by unfold rootedHeatGaussian heatGaussian GeometricBrascampLieb.heatNormalization; fun_prop
  mass := rootedHeatGaussian_mass n hq ht

theorem unitGaussianSet_nonempty (n : ℕ) (q : ℝ) (hq : 0<q) : (unitGaussianSet n q hq).Nonempty :=
  ⟨(heatGaussianInput n hq zero_lt_one).toLp hq,_,rootedHeatGaussian_isGaussian n hq zero_lt_one,rfl⟩

private theorem unit_toLp_eq {n : ℕ} {q : ℝ} (hq : 0<q) {f g : YoungUnitInput n q}
    (h : f.val=g.val) : f.toLp hq=g.toLp hq := by
  apply Lp.ext
  exact (f.toLp_coe hq).trans ((h ▸ g.toLp_coe hq).symm)

theorem unit_dist_act {n : ℕ} {q : ℝ} [Fact (1≤ENNReal.ofReal q)] (hq : 0 < q)
    (f g : YoungUnitInput n q) (A : YoungAffine n) :
    dist ((f.act A hq).toLp hq) ((g.act A hq).toLp hq) = dist (f.toLp hq) (g.toLp hq) := by
  simp only [dist_edist,YoungUnitInput.edist_toLp]
  exact congrArg ENNReal.toReal (A.distance_act f.val g.val hq)

/-- Any sufficiently good Gaussian approximant can be sent to the fixed
reference Gaussian while preserving both the norm and the objective. -/
theorem normalize_near_gaussian {n : ℕ} {q : ℝ} [Fact (1≤ENNReal.ofReal q)] (hq : 0<q)
    (f G : YoungUnitInput n q) (hG : IsEuclideanGaussian G.val) {ρ : ℝ}
    (h : Metric.infDist (f.toLp hq) (unitGaussianSet n q hq) < ρ) :
    ∃ A : YoungAffine n, dist ((f.act A hq).toLp hq) (G.toLp hq) < ρ := by
  obtain ⟨z,⟨g,hg,rfl⟩,hd⟩ := (Metric.infDist_lt_iff (unitGaussianSet_nonempty n q hq)).mp h
  obtain ⟨A,hA⟩ := normalized_gaussian_orbit hq hg hG g.mass G.mass
  exact ⟨A,by rw [← unit_toLp_eq hq (f:=g.act A hq) (g:=G) hA,unit_dist_act]; exact hd⟩

theorem orbit_distance_le_transformed_dist {n : ℕ} {q : ℝ} [Fact (1≤ENNReal.ofReal q)]
    (hq : 0<q) (f g : YoungUnitInput n q) (hg : IsEuclideanGaussian g.val) (A : YoungAffine n) :
    Metric.infDist (f.toLp hq) (unitGaussianSet n q hq) ≤ dist ((f.act A hq).toLp hq) (g.toLp hq) := by
  obtain ⟨v,hv,he⟩ := A.pullback_gaussian (q:=q) hg
  have vm : (∫⁻ x, (v x : ℝ≥0∞)^q ∂euclideanMeasure n)=1 := by
    rw [← A.mass_act v hq, he]; exact g.mass
  let V : YoungUnitInput n q := ⟨v,by
    obtain ⟨c,x₀,M,_,_,_,h⟩ := hv
    have ee : v = fun x => (c*Real.exp (-gaussianQuad M (x-x₀))).toNNReal := by
      funext x; rw [← h,Real.toNNReal_coe]
    rw [ee]; unfold gaussianQuad; fun_prop,vm⟩
  have h := Metric.infDist_le_dist_of_mem (x:=f.toLp hq)
    (show V.toLp hq ∈ unitGaussianSet n q hq from ⟨V,hv,rfl⟩)
  rw [← unit_dist_act hq f V A, unit_toLp_eq hq (f:=V.act A hq) (g:=g) he] at h
  exact h

end LpGowers
