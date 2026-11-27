module

public import LpGowers.CorrelationDefs
public import LpGowers.YoungAffineAction
public import LpGowers.YoungStrongContinuity
public import LpGowers.SharpYoungEquality
public import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Tactic

/-! # Normalized Young inputs and real Lᵖ limits -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LpGowers

/-- A finite, nonnegative representative of unit critical mass. -/
structure YoungUnitInput (n : ℕ) (q : ℝ) where
  val : Rn n → ℝ≥0
  meas : AEMeasurable val (euclideanMeasure n)
  mass : (∫⁻ x, (val x : ℝ≥0∞) ^ q ∂euclideanMeasure n) = 1

namespace YoungUnitInput
variable {n : ℕ} {q : ℝ}
local notation "μ" => euclideanMeasure n

theorem eLpNorm_eq_one (f : YoungUnitInput n q) (hq : 0 < q) :
    eLpNorm (fun x => (f.val x : ℝ)) (ENNReal.ofReal q) μ = 1 := by
  rw [eLpNorm_eq_lp_real f.meas.coe_nnreal_real.aestronglyMeasurable hq]
  simp only [lp, Real.eNorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    f.mass, ENNReal.one_rpow]

theorem memLp (f : YoungUnitInput n q) (hq : 0 < q) :
    MemLp (fun x => (f.val x : ℝ)) (ENNReal.ofReal q) μ := by
  rw [memLp_iff, f.eLpNorm_eq_one hq]
  exact ENNReal.one_lt_top

def toLp (f : YoungUnitInput n q) (hq : 0 < q) : EuclideanLp n q := (f.memLp hq).toLp _

theorem toLp_coe (f : YoungUnitInput n q) (hq : 0 < q) :
    f.toLp hq =ᵐ[μ] fun x => (f.val x : ℝ) := (f.memLp hq).coeFn_toLp

theorem norm_toLp (f : YoungUnitInput n q) (hq : 0 < q) : ‖f.toLp hq‖ = 1 := by
  rw [toLp, Lp.norm_toLp, f.eLpNorm_eq_one hq, ENNReal.toReal_one]

theorem edist_eq_lpDist {u v : EuclideanLp n q} {f g : Rn n → ℝ≥0}
    (hq : 0 < q) (hu : u =ᵐ[μ] fun x => (f x : ℝ)) (hv : v =ᵐ[μ] fun x => (g x : ℝ)) :
    edist u v = lpDist μ q f g := by
  rw [Lp.edist_def, eLpNorm_eq_lp_real ((Lp.aestronglyMeasurable u).sub (Lp.aestronglyMeasurable v)) hq]
  unfold lpDist lp
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  change ‖u x - v x‖ₑ ^ q = edist (f x) (g x) ^ q
  rw [hx, hy, ← eDist_eq_eNorm_sub]
  rfl

theorem edist_toLp (f g : YoungUnitInput n q) (hq : 0 < q) :
    edist (f.toLp hq) (g.toLp hq) = lpDist μ q f.val g.val :=
  edist_eq_lpDist hq (f.toLp_coe hq) (g.toLp_coe hq)

theorem toLp_nonneg (f : YoungUnitInput n q) (hq : 0 < q) : 0 ≤ f.toLp hq := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [f.toLp_coe hq] with x hx
  exact hx.symm ▸ (f.val x).coe_nonneg

/-- Apply an invertible affine normalization, including its determinant amplitude. -/
def act (f : YoungUnitInput n q) (A : YoungAffine n) (hq : 0 < q) : YoungUnitInput n q where
  val := A.act q f.val
  meas := A.aemeasurable f.meas q
  mass := (A.mass_act _ hq).trans f.mass

/-- A strongly convergent normalized extremizing sequence has a Gaussian representative
for its actual limit in the real critical Lebesgue space. -/
theorem gaussian_of_strong_extremizing_limit {s : ℝ} (hs : 1 < s)
    (hq : 0 < criticalExponent 1 s) [Fact (1 ≤ ENNReal.ofReal (criticalExponent 1 s))]
    (f : ℕ → YoungUnitInput n (criticalExponent 1 s)) (u : EuclideanLp n (criticalExponent 1 s))
    (hu : Tendsto (fun j => (f j).toLp hq) atTop (𝓝 u))
    (hM : Tendsto (fun j => cubeMoment 1 n s (f j).val) atTop (𝓝 (youngMomentConstant 1 n s))) :
    ∃ g : YoungUnitInput n (criticalExponent 1 s), IsEuclideanGaussian g.val ∧ g.toLp hq = u := by
  have hpos : 0 ≤ u := le_of_tendsto_of_tendsto' tendsto_const_nhds hu (fun j => (f j).toLp_nonneg hq)
  let v : Rn n → ℝ≥0 := fun x => (u x).toNNReal
  have hv : AEMeasurable v μ := (Lp.aestronglyMeasurable u).aemeasurable.real_toNNReal
  have huv : u =ᵐ[μ] fun x => (v x : ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg u).mpr hpos] with x hx
    exact (Real.coe_toNNReal _ hx).symm
  have hD : Tendsto (fun j => lpDist μ (criticalExponent 1 s) (f j).val v) atTop (𝓝 0) := by
    have hh := hu.edist (tendsto_const_nhds (x := u))
    simpa only [edist_self, edist_eq_lpDist hq ((f _).toLp_coe hq) huv] using hh
  have hqu : 1 ≤ criticalExponent 1 s := by
    simp only [criticalExponent,Nat.cast_one,pow_one]
    exact (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hunit := unit_mass_of_lpDist_tendsto μ hqu (fun j => (f j).meas) hv (fun j => (f j).mass) hD
  have hJ := youngMoment_tendsto_of_lpDist n hs (fun j => (f j).meas) hv (fun j => (f j).mass) hD
  obtain ⟨g,hg,heg⟩ := sharpYoungEquality n s hs v hv hunit (tendsto_nhds_unique hM hJ).le
  let V : YoungUnitInput n (criticalExponent 1 s) := ⟨g,hv.congr heg, by
    rw [← hunit]
    exact lintegral_congr_ae (heg.symm.mono fun x hx => congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞) ^ criticalExponent 1 s) hx)⟩
  refine ⟨V,hg,Lp.ext <| (V.toLp_coe hq).trans ?_⟩
  exact (heg.symm.fun_comp (fun a : ℝ≥0 => (a : ℝ))).trans huv.symm

end YoungUnitInput
end LpGowers
