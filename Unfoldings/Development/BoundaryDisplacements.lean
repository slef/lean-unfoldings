module

public import Unfoldings.Development.BoundaryRays
public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Geometry.CyclicDisplacements

/-! Actual boundary positions and additive displacement around a descendant subtree. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- The placed position of the initial vertex of an actual directed boundary bank. -/
def boundaryPosition (p : C.BoundaryEnd retain) : Plane :=
  D.toPlane (C.vertexPoint retain (C.boundaryEndVertex retain p))

theorem boundaryRay_eq_positions (p : C.BoundaryEnd retain) :
    D.boundaryRay p = D.boundaryPosition (C.boundaryTurn retain p) -
      D.boundaryPosition p := by
  change D.germFarPoint p.val - _ = _
  congr 1
  change _ = D.toPlane (C.vertexPoint retain
    (C.vertexOfCorner retain (C.boundaryTurn retain p).val.1))
  rw [C.boundaryTurn_corner]
  rfl

variable {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
  (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)

include closes in
theorem boundaryRay_eq_cycle_displacement (i : Fin (n + 1)) :
    D.boundaryRay (cycle.point i) =
      D.boundaryPosition (cycle.point (finRotate (n + 1) i)) -
        D.boundaryPosition (cycle.point i) := by
  rw [D.boundaryRay_eq_positions]
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex retain cycle closes i)
  exact congrArg (fun v => D.toPlane (C.vertexPoint retain v) -
    D.boundaryPosition (cycle.point i)) next

include closes in
/-- The sum of every actual bank vector around a closed boundary is zero. -/
theorem sum_boundaryRays_eq_zero :
    (∑ i : Fin (n + 1), D.boundaryRay (cycle.point i)) = 0 := by
  simp only [D.boundaryRay_eq_cycle_displacement cycle closes,
    Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate (n + 1)) (fun i => D.boundaryPosition (cycle.point i)),
    sub_self]

end Unfoldings.FacewiseDevelopment
