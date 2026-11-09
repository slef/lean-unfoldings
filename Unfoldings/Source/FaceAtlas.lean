module

public import Unfoldings.Source.LocalFacePlacement
public import Unfoldings.Geometry.ConvexPatchRigidity

/-!
# Actual face motions are constant on connected retained face regions

Choose the already constructed local source-coordinate patches. Dense face
interiors force overlapping rigid maps to agree. Their motions are locally
constant, and hence one actual rigid motion develops each connected retained
part of an original face, including retained edge and flat-vertex points.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceFaceRegion :
    letI := P.metricSpace
    (source : C.Realization Set.univ) → (f : Face) → Set (C.Cell f) := by
  let := P.metricSpace
  intro source f
  exact {x | C.faceMap Set.univ f x ∉ sourceCutLocus source}

def sourceFaceCoordinates :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      (f : Face) → P.sourceFaceRegion source f → Plane := by
  let := P.metricSpace
  intro source R f x
  exact R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)
    ⟨C.faceMap Set.univ f x.val, x.property⟩

theorem sourceFacePatch_nonempty :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      (x : P.sourceFaceRegion source f),
      Nonempty (LocalRigidPatch (P.sourceFaceRegion source f) (P.sourceFaceCoordinates R f) x) := by
  let := P.metricSpace
  intro source R f x
  obtain ⟨r, positive, A, agrees⟩ := P.exists_local_face_placement R f x.val x.property
  refine ⟨{ radius := r
            positive := positive
            place := A
            inside := fun y near => (agrees y near).1
            agrees := ?_ }⟩
  intro y near
  obtain ⟨p, target⟩ := P.sourcePath_target_surjective source (C.faceMap Set.univ f y.val)
  have outside : p.target ∉ sourceCutLocus source := target.symm ▸ y.property
  have coordinate := R.coordinate_of_sourcePath_off_cut (P.sourcePath_target_surjective source)
    p outside
  have point : (⟨p.target, outside⟩ : ↥((sourceCutLocus source)ᶜ)) =
      ⟨C.faceMap Set.univ f y.val, y.property⟩ := Subtype.ext target
  rw [point] at coordinate
  exact coordinate.trans ((agrees y.val near).2 p target)

def sourceFacePatch :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) → (f : Face) →
      (x : P.sourceFaceRegion source f) →
        LocalRigidPatch (P.sourceFaceRegion source f) (P.sourceFaceCoordinates R f) x := by
  let := P.metricSpace
  intro source R f x
  exact Classical.choice (P.sourceFacePatch_nonempty R f x)

def sourceFaceMotion :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) → (f : Face) →
      P.sourceFaceRegion source f → (Plane ≃ᵃⁱ[ℝ] Plane) := by
  let := P.metricSpace
  intro source R f x
  exact (P.sourceFacePatch R f x).place

theorem sourceFaceMotion_locallyConstant :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face),
      IsLocallyConstant (P.sourceFaceMotion R f) := by
  let := P.metricSpace
  intro source R f
  exact localRigidPatch_motion_locallyConstant (C.triangle f).convex_carrier
    (C.triangle f).interior_nonempty (P.sourceFacePatch R f)

theorem sourceFaceCoordinates_eq_motion :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      (x : P.sourceFaceRegion source f),
      P.sourceFaceCoordinates R f x = P.sourceFaceMotion R f x x.val.val := by
  let := P.metricSpace
  intro source R f x
  exact (P.sourceFacePatch R f x).agrees x (by
    simpa only [dist_self] using (P.sourceFacePatch R f x).positive)

theorem sourceFaceCoordinates_on_connected :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      {S : Set (P.sourceFaceRegion source f)}, IsPreconnected S →
        ∀ {x y}, x ∈ S → y ∈ S →
          P.sourceFaceCoordinates R f y = P.sourceFaceMotion R f x y.val.val := by
  let := P.metricSpace
  intro source R f S connected x y in_x in_y
  rw [P.sourceFaceCoordinates_eq_motion R f y,
    (P.sourceFaceMotion_locallyConstant R f).apply_eq_of_isPreconnected connected in_y in_x]

end Unfoldings.SpatialFolding.ConvexBoundary
