module

public import Unfoldings.Complex.Angles

/-! Intrinsic interior angular defects, grouped by actual retained vertex classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Boundary copies contribute zero to the interior defect. Nonnegativity is a separate theorem. -/
def interiorAngularDefect (retain : Set C.Seam) (v : C.Vertex retain) : ℝ := by
  classical
  exact if C.IsBoundaryVertex retain v then 0 else 2 * Real.pi - C.totalAngle retain v

/-- Sum of actual intrinsic angular defects at the interior vertex copies. -/
def totalInteriorAngularDefect (retain : Set C.Seam) : ℝ :=
  ∑ v : C.Vertex retain, C.interiorAngularDefect retain v

end Unfoldings.TriangleComplex
