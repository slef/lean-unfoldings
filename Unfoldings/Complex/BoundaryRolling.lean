module

public import Unfoldings.Complex.BoundaryContour
public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Geometry.ChainConstruction

/-!
# Roll an actual intrinsic bank contour into the plane

This chain uses the actual original edge lengths and real exterior fan turns.
It is defined even when the enclosed surface is curved. It may overlap and it
need not close: global planar consistency is a theorem to prove when needed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam}

/-- Length of the original edge followed by this actual directed bank. -/
def boundaryBankLength (p : C.BoundaryEnd retain) : ℝ :=
  dist ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2)
    ((C.triangle p.val.1.1).vertex p.val.1.2)

theorem boundaryBankLength_pos (p : C.BoundaryEnd retain) : 0 < C.boundaryBankLength p := by
  apply dist_pos.mpr
  intro same
  apply C.germFarCorner_ne p.val
  exact Prod.ext rfl ((C.triangle p.val.1.1).vertex_injective same)

variable (Q : C.BoundaryContour retain)

/-- Successive actual intrinsic fan turns, without reduction modulo a full turn. -/
def boundaryRollHeading : Fin (Q.length + 1) → ℝ :=
  Fin.partialSum (fun i : Fin Q.length =>
    Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (Q.cycle.point i.succ)))

@[simp] theorem boundaryRollHeading_zero : C.boundaryRollHeading Q 0 = 0 :=
  Fin.partialSum_zero _

theorem boundaryRollHeading_succ (i : Fin Q.length) :
    C.boundaryRollHeading Q i.succ = C.boundaryRollHeading Q i.castSucc +
      (Real.pi - C.totalAngle retain (C.boundaryEndVertex retain (Q.cycle.point i.succ))) :=
  Fin.partialSum_succ _ i

/-- The canonical one-sided bank chain, with its first bank on the positive real axis. -/
def boundaryRoll : PolygonalChain ℂ (Q.length + 1) :=
  PolygonalChain.ofHeadings 0 (fun i => C.boundaryBankLength (Q.cycle.point i))
    (C.boundaryRollHeading Q)

@[simp] theorem boundaryRoll_start : (C.boundaryRoll Q).vertex 0 = 0 :=
  PolygonalChain.ofHeadings_start _ _ _

/-- Every actual bank has exactly its original length, independently of overlap or closure. -/
theorem boundaryRoll_edge_length (i : Fin (Q.length + 1)) :
    ‖(C.boundaryRoll Q).edge i‖ = C.boundaryBankLength (Q.cycle.point i) := by
  rw [boundaryRoll, PolygonalChain.ofHeadings_edge, norm_mul, norm_polarRay, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (C.boundaryBankLength_pos (Q.cycle.point i))]

theorem boundaryRoll_edge_ne_zero (i : Fin (Q.length + 1)) :
    (C.boundaryRoll Q).edge i ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [C.boundaryRoll_edge_length Q]
  exact (C.boundaryBankLength_pos (Q.cycle.point i)).ne'

end Unfoldings.TriangleComplex
