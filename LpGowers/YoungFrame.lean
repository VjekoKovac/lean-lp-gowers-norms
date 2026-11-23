module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # The geometric Brascamp–Lieb frame for sharp diagonal Young

On a Hilbert product the three coisometries are
`(w,z) ↦ -a w + b z`, `(w,z) ↦ a w + b z`, and `(w,z) ↦ w`.
Their weighted norm squares resolve the identity in every dimension.
-/

@[expose] public section
noncomputable section
open scoped BigOperators InnerProduct
namespace LpGowers

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def youngFrameRow (a b : ℝ) : WithLp 2 (V × V) →L[ℝ] V :=
  a • WithLp.fstL 2 ℝ V V + b • WithLp.sndL 2 ℝ V V

omit [CompleteSpace V] in
theorem youngFrameRow_apply (a b : ℝ) (z : WithLp 2 (V × V)) :
    youngFrameRow V a b z = a • z.fst + b • z.snd := rfl

theorem youngFrameRow_adjoint (a b : ℝ) (x : V) :
    (youngFrameRow V a b).adjoint x = WithLp.toLp 2 (a • x,b • x) := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right,WithLp.prod_inner_apply,youngFrameRow_apply]
  simp only [inner_add_left,real_inner_smul_left,real_inner_smul_right]
  rfl

theorem youngFrameRow_coisometry (a b : ℝ) (h : a^2+b^2 = 1) :
    (youngFrameRow V a b).comp (youngFrameRow V a b).adjoint = ContinuousLinearMap.id ℝ V := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,youngFrameRow_adjoint,youngFrameRow_apply,
    WithLp.toLp_fst, WithLp.toLp_snd,smul_smul,← add_smul,← sq,h,one_smul,ContinuousLinearMap.id_apply]

def youngFrameA (s : ℝ) := Real.sqrt (1/(s+1))
def youngFrameB (s : ℝ) := Real.sqrt (s/(s+1))
def youngFrameWeight (s : ℝ) : Fin 3 → ℝ := ![(s+1)/(2*s),(s+1)/(2*s),(s-1)/s]

def youngFrameMap (s : ℝ) : Fin 3 → WithLp 2 (V × V) →L[ℝ] V :=
  ![youngFrameRow V (-youngFrameA s) (youngFrameB s),
    youngFrameRow V (youngFrameA s) (youngFrameB s),youngFrameRow V 1 0]

theorem youngFrameWeight_nonneg {s : ℝ} (hs : 1 ≤ s) (i : Fin 3) : 0 ≤ youngFrameWeight s i := by
  fin_cases i <;> simp [youngFrameWeight] <;> positivity

theorem youngFrameMap_coisometry {s : ℝ} (hs : 0<s) (i : Fin 3) :
    (youngFrameMap V s i).comp (youngFrameMap V s i).adjoint = ContinuousLinearMap.id ℝ V := by
  have ha := Real.sq_sqrt (show 0 ≤ 1/(s+1) by positivity)
  have hb := Real.sq_sqrt (show 0 ≤ s/(s+1) by positivity)
  have hab : youngFrameA s^2 + youngFrameB s^2 = 1 := by
    rw [youngFrameA,youngFrameB,ha,hb]; field_simp; ring
  fin_cases i <;> apply youngFrameRow_coisometry
  · simpa using hab
  · exact hab
  · norm_num

omit [CompleteSpace V] in
theorem youngFrameMap_resolution {s : ℝ} (hs : 0<s) (z : WithLp 2 (V×V)) :
    ∑ i, youngFrameWeight s i * ‖youngFrameMap V s i z‖^2 = ‖z‖^2 := by
  let a := youngFrameA s
  let b := youngFrameB s
  let w := (s+1)/(2*s)
  let v := (s-1)/s
  have ha : a^2 = 1/(s+1) := Real.sq_sqrt (by positivity)
  have hb : b^2 = s/(s+1) := Real.sq_sqrt (by positivity)
  have hw : 2*w*a^2+v=1 := by dsimp only [w,v]; rw [ha]; field_simp; ring
  have hv : 2*w*b^2=1 := by dsimp only [w]; rw [hb]; field_simp
  rw [Fin.sum_univ_three]
  change w*‖(-a) • z.fst + b • z.snd‖^2 + w*‖a • z.fst + b • z.snd‖^2 +
    v*‖(1:ℝ) • z.fst + (0:ℝ) • z.snd‖^2 = ‖z‖^2
  simp only [one_smul,zero_smul,add_zero,← real_inner_self_eq_norm_sq,WithLp.prod_inner_apply,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  change _ = inner ℝ z.fst z.fst + inner ℝ z.snd z.snd
  linear_combination (inner ℝ z.fst z.fst) * hw + (inner ℝ z.snd z.snd) * hv

end LpGowers
