module

public import Unfoldings.Cap.JordanBoundary

/-! Enumerate original geometric Jordan vertices by their unique intrinsic fan copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Every original geometric vertex of the filling has an actual selected intrinsic copy. -/
theorem exists_jordan_vertex (w : C.Vertex Set.univ)
    (member : K.projectedVertex w ∈ PlanarTopology.closedJordanDomain J) :
    ∃ z : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ,
      C.includeRestrictedVertexUniv (K.jordanFaces J) z = w := by
  rw [K.jordanDomain_eq_projectedFace_union jordan contains avoids] at member
  obtain ⟨f, selected, inside⟩ := Set.mem_iUnion₂.mp member
  obtain ⟨i, same⟩ := K.projected_corner_of_vertex_mem w f inside
  refine ⟨(C.restrictFaces (K.jordanFaces J)).vertexOfCorner Set.univ (⟨f, selected⟩, i), ?_⟩
  rw [C.includeRestrictedVertex_ofCorner_univ]
  exact K.projectedVertex_injective ((K.projectedVertex_ofCorner f i).trans same)

open Classical in
/-- The intrinsic vertices enumerate precisely the original geometric vertices in the filling. -/
def jordanVertexEquiv :
    (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ ≃
      {w : C.Vertex Set.univ // K.projectedVertex w ∈ PlanarTopology.closedJordanDomain J} :=
  Equiv.ofBijective (fun z => ⟨C.includeRestrictedVertexUniv (K.jordanFaces J) z, by
    rw [K.projected_includeRestrictedVertex]
    exact (K.jordanIntrinsicHomeomorph jordan contains avoids
      ((C.restrictFaces (K.jordanFaces J)).vertexPoint Set.univ z)).property⟩)
    ⟨fun _ _ same => K.jordan_includeRestrictedVertex_injective jordan contains avoids
      (congrArg Subtype.val same), by
      intro w
      obtain ⟨z, same⟩ := K.exists_jordan_vertex jordan contains avoids w.val w.property
      exact ⟨z, Subtype.ext same⟩⟩

open Classical in
/-- Boundary fan copies enumerate precisely the original vertices on the actual Jordan curve. -/
def jordanBoundaryVertexEquiv :
    (C.restrictFaces (K.jordanFaces J)).BoundaryVertex Set.univ ≃
      {w : C.Vertex Set.univ // K.projectedVertex w ∈ J} :=
  Equiv.ofBijective (fun z => ⟨C.includeRestrictedVertexUniv (K.jordanFaces J) z.val,
    (K.jordan_isBoundaryVertex_iff jordan contains avoids z.val).mp z.property⟩)
    ⟨fun _ _ same => Subtype.ext
      (K.jordan_includeRestrictedVertex_injective jordan contains avoids
        (congrArg Subtype.val same)), by
      intro w
      have member : K.projectedVertex w.val ∈ PlanarTopology.closedJordanDomain J :=
        (isClosed_closure.frontier_subset)
          ((PlanarTopology.frontier_closedJordanDomain jordan).symm ▸ w.property)
      obtain ⟨z, same⟩ := K.exists_jordan_vertex jordan contains avoids w.val member
      refine ⟨⟨z, (K.jordan_isBoundaryVertex_iff jordan contains avoids z).mpr ?_⟩,
        Subtype.ext same⟩
      rw [same]
      exact w.property⟩

end Unfoldings.ConvexCap
