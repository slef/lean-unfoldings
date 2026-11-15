module

public import Unfoldings.Cap.JordanSeamSideSelection
public import Unfoldings.Cap.ProjectedOpening

/-! Construct the unique initial Jordan bank at a directed original seam endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- The geometric filling constructs a unique actual initial bank from the two original
seam sides. Endpoint transport is the original seam isometry's permutation, rather
than a guessed endpoint flag. No selected initial face is an input. -/
theorem existsUnique_jordan_seam_bank (s : C.Seam) (flag : Bool)
    (on_curve : (K.projectedTriangle (C.left s).face).edge (C.left s).edge ⊆ J) :
    ∃! q : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ,
      C.includeRestrictedGerm (K.jordanFaces J) q.val = C.germOfEndpoint (C.left s) flag ∨
        C.includeRestrictedGerm (K.jordanFaces J) q.val =
          C.germOfEndpoint (C.right s) (C.acrossEndpoint s false flag) := by
  let V := K.jordanFaces J
  let R := C.restrictFaces V
  have injective : Function.Injective (fun q : R.BoundaryEnd Set.univ =>
      C.includeRestrictedGerm V q.val) :=
    (C.includeRestrictedGerm_injective V).comp Subtype.val_injective
  have face_selected (q : R.BoundaryEnd Set.univ) (p : C.Germ)
      (named : C.includeRestrictedGerm V q.val = p) : p.1.1 ∈ V := by
    have faces := congrArg (fun r : C.Germ => r.1.1) named
    exact faces ▸ q.val.1.1.property
  have left_curve : (K.projectedTriangle (C.germOfEndpoint (C.left s) flag).1.1).edge
      (C.germEdge (C.germOfEndpoint (C.left s) flag)).edge ⊆ J := by
    simpa only [C.germEdge_germOfEndpoint] using! on_curve
  have exclusive := K.jordan_seam_not_both_selected jordan contains avoids s on_curve
  rcases K.jordan_seam_incident_selected jordan contains avoids s on_curve with first | last
  · obtain ⟨q, named⟩ := K.exists_jordan_bank_of_original_germ jordan contains avoids
      (C.germOfEndpoint (C.left s) flag) first left_curve
    refine ⟨q, Or.inl named, ?_⟩
    intro r same
    rcases same with same | same
    · exact injective (same.trans named.symm)
    · have selected := face_selected r
        (C.germOfEndpoint (C.right s) (C.acrossEndpoint s false flag)) same
      exact (exclusive ⟨first, selected⟩).elim
  · have other_curve : (K.projectedTriangle (C.right s).face).edge (C.right s).edge ⊆ J :=
      (K.projected_seam_edges_eq s).symm.subset.trans on_curve
    have right_curve : (K.projectedTriangle
        (C.germOfEndpoint (C.right s) (C.acrossEndpoint s false flag)).1.1).edge
        (C.germEdge (C.germOfEndpoint (C.right s) (C.acrossEndpoint s false flag))).edge ⊆ J := by
      simpa only [C.germEdge_germOfEndpoint] using! other_curve
    obtain ⟨q, named⟩ := K.exists_jordan_bank_of_original_germ jordan contains avoids
      (C.germOfEndpoint (C.right s) (C.acrossEndpoint s false flag)) last right_curve
    refine ⟨q, Or.inr named, ?_⟩
    intro r same
    rcases same with same | same
    · have selected := face_selected r (C.germOfEndpoint (C.left s) flag) same
      exact (exclusive ⟨selected, last⟩).elim
    · exact injective (same.trans named.symm)

end Unfoldings.ConvexCap
