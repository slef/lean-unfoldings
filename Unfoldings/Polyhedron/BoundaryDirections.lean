module

public import Unfoldings.Polyhedron.GermDirections
public import Unfoldings.Complex.ParentBankEndpoints
public import Unfoldings.Complex.BoundaryCycleEnumeration

/-! Folded bank vectors are differences of actual adjacent boundary vertex positions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

def boundaryPosition (p : C.BoundaryEnd retain) : Space :=
  F.toSpace retain (C.vertexPoint retain (C.boundaryEndVertex retain p))

/-- The intrinsic boundary label keeps the actual original folded endpoint position. -/
theorem boundaryPosition_raw (p : C.BoundaryEnd retain) :
    F.boundaryPosition p = F.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2) :=
  (F.linkGerm_apex retain _ (⟨p.val, rfl⟩ : C.LinkGerm retain _)).symm

theorem germDirection_boundary_positions (p : C.BoundaryEnd retain) :
    F.germDirection p.val =
      F.boundaryPosition (C.boundaryTurn retain p) - F.boundaryPosition p := by
  rw [F.boundaryPosition_raw p]
  change F.germFarPoint p.val - _ = _
  congr 1
  change _ = F.toSpace retain (C.vertexPoint retain
    (C.vertexOfCorner retain (C.boundaryTurn retain p).val.1))
  rw [C.boundaryTurn_corner]
  rfl

@[simp] theorem boundaryPosition_mate (p : C.BoundaryEnd retain) :
    F.boundaryPosition (C.boundaryMate retain p) = F.boundaryPosition p :=
  congrArg (fun w => F.toSpace retain (C.vertexPoint retain w)) (C.boundaryMate_spec retain p).2

@[simp] theorem germDirection_boundaryTurn (p : C.BoundaryEnd retain) :
    F.germDirection (C.boundaryTurn retain p).val = -F.germDirection p.val := by
  rw [F.germDirection_boundary_positions, C.boundaryTurn_involutive,
    F.germDirection_boundary_positions, neg_sub]

/-- Every actual directed boundary adjacency identifies the very same physical edge vector. -/
theorem germDirection_boundary_step {p q : C.BoundaryEnd retain}
    (next : C.boundaryMate retain (C.boundaryTurn retain p) = q) :
    F.germDirection p.val = F.boundaryPosition q - F.boundaryPosition p := by
  rw [F.germDirection_boundary_positions, ← next, F.boundaryPosition_mate]

/-- At the other bank of the same intermediate vertex, the incoming vector is reversed. -/
theorem germDirection_boundary_incoming {p q : C.BoundaryEnd retain}
    (next : C.boundaryMate retain (C.boundaryTurn retain p) = q) :
    F.germDirection (C.boundaryMate retain q).val =
      F.boundaryPosition p - F.boundaryPosition q := by
  have paired : C.boundaryMate retain q = C.boundaryTurn retain p := by
    rw [← next, C.boundaryMate_involutive]
  rw [paired, F.germDirection_boundaryTurn, F.germDirection_boundary_step next, neg_sub]

end Unfoldings.SpatialFolding
