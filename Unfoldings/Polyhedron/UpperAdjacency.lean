module

public import Unfoldings.Polyhedron.UpperRoof
public import Unfoldings.Geometry.TriangleUnionInterior

/-! Geometric upper-face adjacency is exactly adjacency across an original whole seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.SupportingNormals

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (N : F.SupportingNormals)

theorem upper_edgeAdjacent_iff (P : F.ConvexBoundary) (f g : N.UpperFace) :
    TriangleFamily.EdgeAdjacent N.upperTriangle f g ↔
      f ≠ g ∧ ∃ s : C.Seam,
        ((C.left s).face = f.val ∧ (C.right s).face = g.val) ∨
          ((C.left s).face = g.val ∧ (C.right s).face = f.val) := by
  constructor
  · rintro ⟨different, e, d, same⟩
    obtain ⟨s, ⟨left, right⟩ | ⟨left, right⟩⟩ :=
      N.upper_exists_seam P f g different e d same
    · exact ⟨different, s, Or.inl ⟨congrArg EdgeRef.face left, congrArg EdgeRef.face right⟩⟩
    · exact ⟨different, s, Or.inr ⟨congrArg EdgeRef.face left, congrArg EdgeRef.face right⟩⟩
  · rintro ⟨different, s, ⟨left, right⟩ | ⟨left, right⟩⟩
    · refine ⟨different, (C.left s).edge, (C.right s).edge, ?_⟩
      rw [N.upperTriangle_edge, N.upperTriangle_edge, ← left, ← right]
      exact N.projected_seam_edges_eq s
    · refine ⟨different, (C.right s).edge, (C.left s).edge, ?_⟩
      rw [N.upperTriangle_edge, N.upperTriangle_edge, ← right, ← left]
      exact (N.projected_seam_edges_eq s).symm

end Unfoldings.SpatialFolding.SupportingNormals
