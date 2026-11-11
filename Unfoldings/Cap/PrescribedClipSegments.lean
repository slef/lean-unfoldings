module

public import Unfoldings.Cap.ClipEdgeLift
public import Unfoldings.Geometry.TriangleWithEdge

/-!
# Meshing prescribed whole segments into the actual physical roof

Use all three supporting coordinates of an auxiliary triangle for each segment.
The endpoint constraints ensure that segments, rather than merely their entire
supporting lines, become exact unions of whole fine edges. Original cap edges
are preserved simultaneously.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Type} (first last : J → Plane) (different : ∀ j, first j ≠ last j)

def originalAndSegmentEquations :
    (Fin (Fintype.card Face) × Fin 3) ⊕ (J × Fin 3) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim K.originalEdgeEquations
    (fun i => (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord i.2)

theorem originalAndSegmentEquations_ne_zero
    (i : (Fin (Fintype.card Face) × Fin 3) ⊕ (J × Fin 3)) :
    K.originalAndSegmentEquations first last different i ≠ 0 := by
  cases i with
  | inl i => exact K.originalEdgeEquations_ne_zero i
  | inr i => exact (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord_ne_zero i.2

namespace ClipSpatialTriangles

variable {K first last different} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- Mesh arbitrary finite genuine segments together with all original input edges. -/
def preserveSegments [Finite J] (lower : Z < 0) :
    K.LineAlignedClip Z (K.originalAndSegmentEquations first last different) :=
  T.alignToLines _ (K.originalAndSegmentEquations_ne_zero first last different) lower

end ClipSpatialTriangles

namespace LineAlignedClip

variable {K first last different} {Z : ℝ}
  (L : K.LineAlignedClip Z (K.originalAndSegmentEquations first last different))

/-- Retain the already proved original-cut interface after adjoining segment constraints. -/
def originalPart : K.LineAlignedClip Z K.originalEdgeEquations where
  partition := L.partition
  conforming := L.conforming
  signs i j := L.signs i (Sum.inl j)
  side i p member j := L.side i p member (Sum.inl j)

/-- A prescribed closed segment inside the clip is exactly the union of whole fine edges in it. -/
theorem segment_eq_union_subedges (j : J)
    (first_member : first j ∈ K.clipFootprint Z) (last_member : last j ∈ K.clipFootprint Z) :
    segment ℝ (first j) (last j) =
      ⋃ a : {a : L.partition.Index × Fin 3 //
          (L.partition.projectedTriangle a.1).edge a.2 ⊆ segment ℝ (first j) (last j)},
        (L.partition.projectedTriangle a.val.1).edge a.val.2 := by
  let := L.partition.finite
  let U := triangleWithEdge (first j) (last j) (different j)
  have cover : U.edge 0 ⊆ ⋃ i, (L.partition.projectedTriangle i).carrier :=
    ((K.convex_clipFootprint Z).segment_subset first_member last_member).trans
      L.partition.cover.subset
  exact TriangleFamily.edge_eq_union_subedges L.partition.projectedTriangle U 0 cover
    (fun i k => L.signs i (Sum.inr (j, k)))
    (fun i k p member => L.side i p member (Sum.inr (j, k)))

/-- The same exact coverage holds for the actual roof lift, with physical fine edges. -/
theorem spatial_segment_eq_union_subedges (j : J)
    (first_member : first j ∈ K.clipFootprint Z) (last_member : last j ∈ K.clipFootprint Z) :
    K.roofPoint '' segment ℝ (first j) (last j) =
      ⋃ a : {a : L.partition.Index × Fin 3 //
          (L.partition.projectedTriangle a.1).edge a.2 ⊆ segment ℝ (first j) (last j)},
        L.partition.placement a.val.1 '' (L.partition.triangle a.val.1).edge a.val.2 := by
  let E := {a : L.partition.Index × Fin 3 //
    (L.partition.projectedTriangle a.1).edge a.2 ⊆ segment ℝ (first j) (last j)}
  calc
    K.roofPoint '' segment ℝ (first j) (last j) =
        K.roofPoint '' (⋃ a : E, (L.partition.projectedTriangle a.val.1).edge a.val.2) :=
      congrArg (fun S : Set Plane => K.roofPoint '' S)
        (L.segment_eq_union_subedges j first_member last_member)
    _ = ⋃ a : E, K.roofPoint '' (L.partition.projectedTriangle a.val.1).edge a.val.2 :=
      Set.image_iUnion
    _ = ⋃ a : E, L.partition.placement a.val.1 ''
        (L.partition.triangle a.val.1).edge a.val.2 :=
      Set.iUnion_congr (fun a =>
        (L.partition.edge_image_eq_roofPoint_image a.val.1 a.val.2).symm)

end LineAlignedClip
end Unfoldings.ConvexCap
