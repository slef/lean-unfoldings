module

public import Unfoldings.Polyhedron.VertexFigure
public import Unfoldings.Polyhedron.FaceSupport

/-!
# The actual spatial boundary of a planar vertex figure

The plane of every original face supports the body. Hence any figure point
in an original face lies on the planar figure boundary: an interior local
maximum of the pulled-back support functional would force it to be constant,
contradicting strict inequality at the figure's interior center.

Conversely a planar boundary point cannot map to the spatial interior.
This identifies the figure boundary exactly with the original spatial
surface intersected with its transverse level plane.
-/

@[expose] public section

open Topology

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)

include P

theorem figure_face_mem_frontier (face : Face) (p : Plane)
    (in_face : V.place p ∈ F.faceImage face) : p ∈ frontier V.carrier := by
  have member : p ∈ V.carrier := F.faceImage_subset_vertexHull face in_face
  refine ⟨subset_closure member, ?_⟩
  intro inside
  obtain ⟨f, a, _nonzero, supported, strict, face_level⟩ := P.exists_face_support face
  have at_p : f (V.place p) = a := by
    obtain ⟨q, _hq, image⟩ := in_face
    rw [← image]
    exact face_level q
  let g : Plane →ᵃ[ℝ] ℝ := f.toLinearMap.toAffineMap.comp V.place.toAffineMap
  have maximum : IsLocalMax g p := by
    change ∀ᶠ q in 𝓝 p, f (V.place q) ≤ f (V.place p)
    exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp inside)
      (fun q hq => (supported (V.place q) hq).trans_eq at_p.symm)
  have constant : f (V.place 0) = f (V.place p) := affine_eq_at_of_localMax g p maximum 0
  rw [V.place_zero, at_p] at constant
  exact (strict V.center V.center_inside).ne constant

theorem figure_frontier_iff_surface (p : Plane) :
    p ∈ frontier V.carrier ↔ V.place p ∈ F.surface := by
  constructor
  · intro boundary
    have member : p ∈ V.carrier := by
      rw [← V.compact_carrier.isClosed.closure_eq]
      exact boundary.1
    have outside : V.place p ∉ interior F.vertexHull := by
      intro inside
      exact boundary.2 (preimage_interior_subset_interior_preimage V.place.continuous inside)
    rw [P.boundary]
    exact ⟨subset_closure member, outside⟩
  · intro surface
    obtain ⟨face, in_face⟩ := Set.mem_iUnion.mp surface
    exact P.figure_face_mem_frontier V face p in_face

theorem image_figure_frontier : V.place '' frontier V.carrier =
    F.surface ∩
      {z | V.functional (z - F.toSpace Set.univ (C.vertexPoint Set.univ v)) = V.level} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(P.figure_frontier_iff_surface V p).mp hp, ?_⟩
    exact V.range_place.le ⟨p, rfl⟩
  · rintro ⟨surface, level⟩
    obtain ⟨p, image⟩ := V.range_place.ge level
    refine ⟨p, (P.figure_frontier_iff_surface V p).mpr ?_, image⟩
    rw [image]
    exact surface

end Unfoldings.SpatialFolding.ConvexBoundary
