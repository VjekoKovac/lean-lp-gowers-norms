module

public import LpGowers.YoungFrame
public import GeometricBrascampLieb.FrameDatum
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-! # Equality in the quadratic defect for the diagonal Young frame

The two copies of the same logarithmic gradient on the first two rows
make the gradient's first differences translation-invariant. Continuity
then gives a real affine map.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace LpGowers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The pointwise vector data used by the heat-flow defect of the diagonal Young datum. -/
def youngFrameFields (s : ℝ) (F H : V → V) (z : WithLp 2 (V × V)) : Fin 3 → V :=
  ![F (youngFrameMap V s 0 z), F (youngFrameMap V s 1 z), H (youngFrameMap V s 2 z)]

/-- Vanishing of the geometric Brascamp–Lieb defect everywhere forces the repeated
continuous field in the diagonal Young inequality to be affine. -/
theorem affine_of_youngFrame_defect_zero {s : ℝ} (hs : 1 < s)
    (F H : V → V) (hF : Continuous F)
    (hzero : ∀ z : WithLp 2 (V × V),
      let v := youngFrameFields s F H z
      (∑ i, youngFrameWeight s i * ‖v i‖ ^ 2) =
        ‖∑ i, youngFrameWeight s i • (youngFrameMap V s i).adjoint (v i)‖ ^ 2) :
    ∃ L : V →L[ℝ] V, ∀ x, F x = L x + F 0 := by
  let D : GeometricBrascampLieb.Datum (Fin 3) (WithLp 2 (V × V)) (fun _ => V) :=
    .ofNormSq (youngFrameMap V s) (youngFrameWeight s) (youngFrameWeight_nonneg hs.le)
      (youngFrameMap_coisometry V (zero_lt_one.trans hs))
      (youngFrameMap_resolution V (zero_lt_one.trans hs))
  have hpos (i : Fin 3) : 0 < D.weight i := by
    change 0 < youngFrameWeight s i
    fin_cases i <;> simp [youngFrameWeight] <;> positivity
  have hcompat (z : WithLp 2 (V × V)) (i : Fin 3) :
      youngFrameFields s F H z i = D.map i (D.synthesis (youngFrameFields s F H z)) := by
    let v := youngFrameFields s F H z
    have hz : (∑ i, D.weight i * ‖v i‖ ^ 2) = ‖D.synthesis v‖ ^ 2 := hzero z
    have hsum := D.defect_eq_sum_sq v
    rw [hz, sub_self] at hsum
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))).mp hsum.symm i (Finset.mem_univ i)
    have hnorm := (mul_eq_zero.mp hi).resolve_left (hpos i).ne'
    simpa only [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] using hnorm
  let a := youngFrameA s
  let b := youngFrameB s
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hdiff (w k : V) : F (a • w + b • k) - F ((-a) • w + b • k) =
      (2 * a) • H w := by
    let z := WithLp.toLp 2 (w,k)
    let y := D.synthesis (youngFrameFields s F H z)
    have h₀ : F ((-a) • w + b • k) = (-a) • y.fst + b • y.snd := hcompat z 0
    have h₁ : F (a • w + b • k) = a • y.fst + b • y.snd := hcompat z 1
    have h₂ := hcompat z 2
    change H ((1 : ℝ) • w + (0 : ℝ) • k) = (1 : ℝ) • y.fst + (0 : ℝ) • y.snd at h₂
    simp only [one_smul,zero_smul,add_zero] at h₂
    rw [h₀,h₁,h₂]
    module
  have hdelta (x t : V) : F (x+t) - F x = (2*a) • H ((2*a)⁻¹ • t) := by
    let w := (2*a)⁻¹ • t
    let k := b⁻¹ • (x+a • w)
    have hw : (2*a) • w = t := by
      dsimp only [w]; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
    have hk : b • k = x+a • w := by
      dsimp only [k]; rw [smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
    have hmain := hdiff w k
    rw [hk] at hmain
    have hminus : (-a) • w + (x+a • w) = x := by module
    have hplus : a • w + (x+a • w) = x+t := by rw [← hw]; module
    simpa only [hminus,hplus] using hmain
  let L : V →+ V := {
    toFun := fun x => F x - F 0
    map_zero' := sub_self _
    map_add' := by
      intro x t
      have h := (hdelta x t).trans (hdelta 0 t).symm
      simp only [zero_add] at h
      calc
        F (x + t) - F 0 = (F (x+t) - F x) + (F x - F 0) := by abel
        _ = _ := by rw [h]; abel }
  have hc : Continuous L := hF.sub continuous_const
  refine ⟨L.toRealLinearMap hc, ?_⟩
  intro x
  change F x = (F x - F 0) + F 0
  abel

end LpGowers
