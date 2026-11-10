module

public import Unfoldings.Development.Uniqueness
public import Unfoldings.Geometry.AffineEnd

/-! Normalize an outward development by any prescribed root face motion. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem rigid_disjoint_interiors (A : Plane ≃ᵃⁱ[ℝ] Plane) {s t : Set Plane}
    (disjoint : Disjoint (interior s) (interior t)) :
    Disjoint (interior (A '' s)) (interior (A '' t)) := by
  rw [← rigid_image_interior, ← rigid_image_interior]
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, first⟩ ⟨y, hy, last⟩
  exact Set.disjoint_left.mp disjoint hx (A.injective (last.trans first.symm) ▸ hy)

namespace FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (E : FacewiseDevelopment C retain)

/-- Apply one global planar rigid motion to every face. -/
def postcompose (A : Plane ≃ᵃⁱ[ℝ] Plane) : FacewiseDevelopment C retain where
  place f := (E.place f).trans A
  joined s kept x := congrArg A (E.joined s kept x)
  opposite s kept := by
    apply (C.triangle (C.left s).face).placed_opposite_of_disjoint
      (C.triangle (C.right s).face) (C.left s).edge (C.right s).edge (C.identify s)
      ((E.place (C.left s).face).trans A) ((E.place (C.right s).face).trans A)
      (fun x => congrArg A (E.joined s kept x))
    have nested (f : Face) :
        (E.place f).trans A '' (C.triangle f).carrier = A '' E.faceImage f := by
      change (E.place f).trans A '' (C.triangle f).carrier =
        A '' (E.place f '' (C.triangle f).carrier)
      rw [Set.image_image]
      rfl
    rw [nested, nested]
    exact rigid_disjoint_interiors A (E.hinge_nonoverlap s kept)


@[simp] theorem postcompose_toPlane (A : Plane ≃ᵃⁱ[ℝ] Plane) (x : C.Realization retain) :
    (E.postcompose A).toPlane x = A (E.toPlane x) := by
  obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  rfl

theorem isometry_postcompose (A : Plane ≃ᵃⁱ[ℝ] Plane) {s : Set (C.Realization retain)}
    (isometric : Isometry (fun x : s => E.toPlane x.val)) :
    Isometry (fun x : s => (E.postcompose A).toPlane x.val) := by
  intro x y
  change edist ((E.postcompose A).toPlane x.val) ((E.postcompose A).toPlane y.val) = edist x y
  rw [postcompose_toPlane, postcompose_toPlane, A.isometry.edist_eq]
  exact isometric x y

/-- Fix the root face to an arbitrary rigid placement, with all other placements transported. -/
def normalize (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) : FacewiseDevelopment C retain :=
  E.postcompose ((E.place root).symm.trans target)

@[simp] theorem normalize_root (root : Face) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    (E.normalize root target).place root = target := by
  apply AffineIsometryEquiv.ext
  intro x
  change target ((E.place root).symm (E.place root x)) = target x
  rw [AffineIsometryEquiv.symm_apply_apply]

end FacewiseDevelopment
end Unfoldings
