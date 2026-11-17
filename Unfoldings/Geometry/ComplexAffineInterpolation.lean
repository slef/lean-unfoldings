module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.Ring

/-! Complex affine interpolation preserves real coordinates and their fixed scale. -/

@[expose] public section

namespace Unfoldings

theorem complex_lineMap_real_mul (s t u c : ℝ) :
    AffineMap.lineMap (((s * c : ℝ) : ℂ)) (((t * c : ℝ) : ℂ)) u =
      (((AffineMap.lineMap s t u) * c : ℝ) : ℂ) := by
  simp only [AffineMap.lineMap_apply_module', smul_eq_mul, Complex.real_smul, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

end Unfoldings
