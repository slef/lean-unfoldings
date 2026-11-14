module

public import Unfoldings.Complex.AffineProjectionClasses
public import Unfoldings.Development

/-! Actual nonoverlapping projected triangles supply a global identity development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)
  (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)

include joined in
theorem affineProjected_seam_faces_ne (s : C.Seam) : (C.left s).face ≠ (C.right s).face := by
  intro same
  have edges : (C.left s).edge = (C.right s).edge :=
    (C.affineProjectedTriangle A (C.left s).face).edge_injective (by
      simpa only [← same] using C.affineProjected_seam_edges A joined s)
  have ext {a b : EdgeRef Face} (faces : a.face = b.face) (indices : a.edge = b.edge) :
      a = b := by
    cases a
    cases b
    cases faces
    cases indices
    rfl
  exact C.distinct s (ext same edges)

/-- A separate planar development of the projected metric, with strict opposite-side hinges. -/
def affineProjectionDevelopment
    (separated : Pairwise (fun f g =>
      Disjoint (interior (C.affineProjectedTriangle A f).carrier)
        (interior (C.affineProjectedTriangle A g).carrier))) :
    FacewiseDevelopment (C.affineProjectionComplex A joined) Set.univ where
  place _ := AffineIsometryEquiv.refl ℝ Plane
  joined _ _ _ := rfl
  opposite s _ :=
    (C.affineProjectedTriangle A (C.left s).face).opposite_of_shared_edge
      (C.affineProjectedTriangle A (C.right s).face) (C.left s).edge (C.right s).edge
      (C.affineProjected_seam_edges A joined s)
      (separated (C.affineProjected_seam_faces_ne A joined s))

end Unfoldings.TriangleComplex
