module

public import Unfoldings.Cap.IntrinsicSectionTurns
public import Unfoldings.Development.AdditionalCuts
public import Unfoldings.Development.Normalization

/-! The constructed intrinsic seam turn is the actual angle in every retained development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Outward hinge rigidity makes this intrinsic turn independent of the development. -/
theorem angle_eq_intrinsicSectionTurn (s : C.Seam) (kept : s ∈ retain) (direction : Plane) :
    InnerProductGeometry.angle (D.developedDirection K (C.left s).face direction)
      (D.developedDirection K (C.right s).face direction) = K.intrinsicSectionTurn s direction := by
  let F := C.singleSeamDevelopment s (K.folding.incident_faces_ne s)
  let A := (D.place (C.left s).face).symm
  let E := (D.cut (show ({s} : Set C.Seam) ⊆ retain from
    Set.singleton_subset_iff.mpr kept)).postcompose A
  have left : E.place (C.left s).face = F.place (C.left s).face := by
    have right_side : F.place (C.left s).face = AffineIsometryEquiv.refl ℝ Plane :=
      C.hingeFrame_left s (K.folding.incident_faces_ne s)
    rw [right_side]
    apply AffineIsometryEquiv.ext
    intro x
    exact (D.place (C.left s).face).symm_apply_apply x
  have right : E.place (C.right s).face = F.place (C.right s).face :=
    E.place_eq_across F s (Set.mem_singleton s) false left
  have first_direction : E.developedDirection K (C.left s).face direction =
      F.developedDirection K (C.left s).face direction :=
    congrArg (fun B : Plane ≃ᵃⁱ[ℝ] Plane =>
      B.linear (K.pullbackDirection (C.left s).face direction)) left
  have last_direction : E.developedDirection K (C.right s).face direction =
      F.developedDirection K (C.right s).face direction :=
    congrArg (fun B : Plane ≃ᵃⁱ[ℝ] Plane =>
      B.linear (K.pullbackDirection (C.right s).face direction)) right
  have invariant : InnerProductGeometry.angle (E.developedDirection K (C.left s).face direction)
      (E.developedDirection K (C.right s).face direction) =
      InnerProductGeometry.angle (D.developedDirection K (C.left s).face direction)
        (D.developedDirection K (C.right s).face direction) := by
    change InnerProductGeometry.angle
      (A.toAffineIsometry.linearIsometry (D.developedDirection K (C.left s).face direction))
      (A.toAffineIsometry.linearIsometry (D.developedDirection K (C.right s).face direction)) = _
    exact A.toAffineIsometry.linearIsometry.angle_map _ _
  rw [← invariant, first_direction, last_direction]
  rfl

end Unfoldings.FacewiseDevelopment
