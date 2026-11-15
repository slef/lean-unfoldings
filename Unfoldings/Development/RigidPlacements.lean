module

public import Unfoldings.Development.AffineProjection

/-! Separated actual rigid triangle placements supply the opposite-side development condition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Construct a development from actual joined rigid placements with disjoint face interiors. -/
def ofRigidPlacements (place : Face → Plane ≃ᵃⁱ[ℝ] Plane)
    (joined : ∀ s x, place (C.left s).face x.val = place (C.right s).face (C.identify s x).val)
    (separated : Pairwise (fun f g =>
      Disjoint (interior (C.affineProjectedTriangle (fun i => (place i).toAffineEquiv) f).carrier)
        (interior (C.affineProjectedTriangle (fun i => (place i).toAffineEquiv) g).carrier))) :
    FacewiseDevelopment C Set.univ where
  place := place
  joined s _ x := joined s x
  opposite s _ :=
    (C.affineProjectedTriangle (fun i => (place i).toAffineEquiv) (C.left s).face)
      |>.opposite_of_shared_edge
        (C.affineProjectedTriangle (fun i => (place i).toAffineEquiv) (C.right s).face)
        (C.left s).edge (C.right s).edge
        (C.affineProjected_seam_edges (fun i => (place i).toAffineEquiv) joined s)
        (separated (C.affineProjected_seam_faces_ne (fun i => (place i).toAffineEquiv) joined s))

end Unfoldings.FacewiseDevelopment
