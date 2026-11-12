module

public import Unfoldings.Development.Normalization

/-! Global rigid motions and root normalization preserve actual face-interior nonoverlap. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (E : FacewiseDevelopment C retain)

theorem postcompose_nonoverlapping_iff (A : Plane ≃ᵃⁱ[ℝ] Plane) :
    (E.postcompose A).Nonoverlapping ↔ E.Nonoverlapping := by
  have images (f) : (E.postcompose A).faceImage f = A '' E.faceImage f := by
    change ((E.place f).trans A) '' (C.triangle f).carrier =
      A '' (E.place f '' (C.triangle f).carrier)
    rw [Set.image_image]
    rfl
  constructor
  · intro nonoverlap f g different
    have back := rigid_disjoint_interiors A.symm (nonoverlap f g different)
    rw [images f, images g, Set.image_image, Set.image_image] at back
    simp only [AffineIsometryEquiv.symm_apply_apply] at back
    change Disjoint (interior (id '' E.faceImage f)) (interior (id '' E.faceImage g)) at back
    simpa only [Set.image_id] using back
  · intro nonoverlap f g different
    rw [images f, images g]
    exact rigid_disjoint_interiors A (nonoverlap f g different)

theorem normalize_nonoverlapping_iff (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    (E.normalize root target).Nonoverlapping ↔ E.Nonoverlapping :=
  E.postcompose_nonoverlapping_iff _

theorem nonoverlapping_iff_of_duallyConnected (F : FacewiseDevelopment C retain)
    (connected : C.DuallyConnected retain) (root : Face) : E.Nonoverlapping ↔ F.Nonoverlapping := by
  have same : F.normalize root (E.place root) = E :=
    (F.normalize root (E.place root)).eq_of_root E connected root (F.normalize_root root _)
  simpa only [same] using F.normalize_nonoverlapping_iff root (E.place root)

end Unfoldings.FacewiseDevelopment
