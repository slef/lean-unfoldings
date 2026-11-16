module

public import Unfoldings.Geometry.SpatialGraphPartition

/-! Restrict and change graph-patch presentations while retaining every actual physical cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialGraphPartition

universe u

variable {height : Plane → ℝ} {region : Set Plane} {A : Type u}
  (P : SpatialGraphPartition height region A)

/-- Restrict to actual whole cells with their exact covered region and original rigid frames. -/
def restrict (selected : A → Prop) (s : Set Plane)
    (cover : s = ⋃ a : {a // selected a}, P.footprint a.val) :
    SpatialGraphPartition height s {a // selected a} where
  footprint a := P.footprint a.val
  plane a := P.plane a.val
  closed a := P.closed a.val
  convex a := P.convex a.val
  full a := P.full a.val
  disjoint a b different := P.disjoint a.val b.val (fun equal => different (Subtype.ext equal))
  cover := cover
  active a p member := P.active a.val p member

/-- Re-express the covered region without altering any original physical cell. -/
def withRegion (other : Set Plane) (same : other = region) :
    SpatialGraphPartition height other A where
  footprint := P.footprint
  plane := P.plane
  closed := P.closed
  convex := P.convex
  full := P.full
  disjoint := P.disjoint
  cover := same.trans P.cover
  active := P.active

/-- A different height formula for the same actual patch preserves all original physical cells.
No agreement outside the covered patch is needed. -/
def withHeight (other : Plane → ℝ) (agrees : Set.EqOn other height region) :
    SpatialGraphPartition other region A where
  footprint := P.footprint
  plane := P.plane
  closed := P.closed
  convex := P.convex
  full := P.full
  disjoint := P.disjoint
  cover := P.cover
  active a p member := (agrees (P.footprint_subset_region a member)).trans (P.active a p member)

variable [Finite A]

/-- Changing only the region presentation preserves all actual cut-metric copies. -/
def withRegionCutEquiv (other : Set Plane) (same : other = region) (cuts : Set Plane) :
    P.Cut cuts ≃ᵢ (P.withRegion other same).Cut cuts := IsometryEquiv.refl _

/-- Re-expressing graph height preserves the literal cut metric and all its copies. -/
def withHeightCutEquiv (other : Plane → ℝ) (agrees : Set.EqOn other height region)
    (cuts : Set Plane) : P.Cut cuts ≃ᵢ (P.withHeight other agrees).Cut cuts :=
  IsometryEquiv.refl _

end Unfoldings.SpatialGraphPartition
