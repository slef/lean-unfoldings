module

public import Unfoldings.Geometry.SpatialEnvelopeTriangles
public import Unfoldings.Geometry.SpatialGraphPresentations

/-! Actual completion triangles are graph-patch cells in their original rigid frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

/-- Present the actual finite physical mesh as a graph patch, retaining every original triangle. -/
def graphPartition : SpatialGraphPartition (height family) (clip family Z) T.Index where
  footprint a := (T.projectedTriangle a).carrier
  plane a := family (T.support a)
  closed a := (T.projectedTriangle a).compact_carrier.isClosed
  convex a := (T.projectedTriangle a).convex_carrier
  full a := (T.projectedTriangle a).interior_nonempty
  disjoint _ _ different := T.separated different
  cover := T.cover
  active := T.active

/-- The graph-patch cells are precisely the original placed spatial triangles. -/
theorem graphPartition_spatialCell (a : T.Index) :
    T.graphPartition.spatialCell a = T.placement a '' (T.triangle a).carrier := by
  rw [T.triangle_carrier]
  rfl

/-- Present the actual mesh on a region with any height formula agreeing there.
The original physical triangles and their frames remain literal cells of the patch. -/
def graphPartitionOn (height' : Plane → ℝ) (region : Set Plane)
    (domain : region = clip family Z) (agrees : Set.EqOn height' (height family) region) :
    SpatialGraphPartition height' region T.Index :=
  (T.graphPartition.withRegion region domain).withHeight height' agrees

local instance graphTriangulationIndexFinite : Finite T.Index := T.finite

/-- Domain and height presentation changes retain the exact physical triangular cut. -/
def graphPartitionOnCutEquiv (height' : Plane → ℝ) (region : Set Plane)
    (domain : region = clip family Z) (agrees : Set.EqOn height' (height family) region)
    (cuts : Set Plane) : T.graphPartition.Cut cuts ≃ᵢ
      (T.graphPartitionOn height' region domain agrees).Cut cuts := IsometryEquiv.refl _

theorem fold_graphPartitionOnCutEquiv (height' : Plane → ℝ) (region : Set Plane)
    (domain : region = clip family Z) (agrees : Set.EqOn height' (height family) region)
    (cuts : Set Plane) (x : T.graphPartition.Cut cuts) :
    (T.graphPartitionOn height' region domain agrees).fold cuts
      (T.graphPartitionOnCutEquiv height' region domain agrees cuts x) =
        T.graphPartition.fold cuts x := rfl

end Unfoldings.SpatialEnvelope.Triangulation
