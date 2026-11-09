module

public import Unfoldings.Source.HingePlacement
public import Unfoldings.Source.FaceMotionUniqueness

/-! Actual source-face motions use the deterministic outward hinge transition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceFaceMotion_seam_nonvertex :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (s : C.Seam)
      (q : (C.triangle (C.left s).face).Edge (C.left s).edge),
      ¬ (C.triangle (C.left s).face).IsVertex q →
      ∀ left_outside : C.faceMap Set.univ (C.left s).face
          ((C.triangle (C.left s).face).edgeMap (C.left s).edge q) ∉ sourceCutLocus source,
        ∀ right_outside : C.faceMap Set.univ (C.right s).face
            ((C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s q)) ∉
              sourceCutLocus source,
          P.sourceFaceMotion R (C.right s).face
            ⟨(C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s q),
              right_outside⟩ =
          (C.seamHinge s).place.trans (P.sourceFaceMotion R (C.left s).face
            ⟨(C.triangle (C.left s).face).edgeMap (C.left s).edge q, left_outside⟩) := by
  let := P.metricSpace
  intro source R s q regular left_outside right_outside
  let l : P.sourceFaceRegion source (C.left s).face :=
    ⟨(C.triangle (C.left s).face).edgeMap (C.left s).edge q, left_outside⟩
  let r : P.sourceFaceRegion source (C.right s).face :=
    ⟨(C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s q), right_outside⟩
  obtain ⟨δ, positive, A, coordinates⟩ := P.exists_source_hinge_placement R s q regular left_outside
  have left_motion : P.sourceFaceMotion R (C.left s).face l = A := by
    apply P.sourceFaceMotion_eq_of_patch R _ l A positive
    intro y near
    have close : dist (C.hingeCoordinates s ⟨(C.left s).face, y⟩) q.val < δ := by
      rw [C.hingeCoordinates_left s (F.incident_faces_ne s)]
      exact near
    obtain ⟨outside, equal⟩ := coordinates ⟨(C.left s).face, y⟩ (Or.inl rfl) close
    refine ⟨outside, ?_⟩
    have actual : P.extendedSourceCoordinates R (C.faceMap Set.univ (C.left s).face y) =
        P.sourceFaceCoordinates R (C.left s).face ⟨y, outside⟩ :=
      P.extendedSourceCoordinates_agrees R ⟨_, outside⟩
    exact actual.symm.trans (equal.trans (congrArg A
      (C.hingeCoordinates_left s (F.incident_faces_ne s) y)))
  have right_motion : P.sourceFaceMotion R (C.right s).face r = (C.seamHinge s).place.trans A := by
    apply P.sourceFaceMotion_eq_of_patch R _ r _ positive
    intro y near
    have distance : dist (C.hingeCoordinates s ⟨(C.right s).face, y⟩) q.val =
        dist y.val (C.identify s q).val := by
      rw [C.hingeCoordinates_right, ← (C.seamHinge s).joined q,
        (C.seamHinge s).place.isometry.dist_eq]
    have close : dist (C.hingeCoordinates s ⟨(C.right s).face, y⟩) q.val < δ := by
      rw [distance]
      exact near
    obtain ⟨outside, equal⟩ := coordinates ⟨(C.right s).face, y⟩ (Or.inr rfl) close
    refine ⟨outside, ?_⟩
    have actual : P.extendedSourceCoordinates R (C.faceMap Set.univ (C.right s).face y) =
        P.sourceFaceCoordinates R (C.right s).face ⟨y, outside⟩ :=
      P.extendedSourceCoordinates_agrees R ⟨_, outside⟩
    exact actual.symm.trans (equal.trans (congrArg A (C.hingeCoordinates_right s y)))
  change P.sourceFaceMotion R (C.right s).face r =
    (C.seamHinge s).place.trans (P.sourceFaceMotion R (C.left s).face l)
  rw [right_motion, left_motion]

end Unfoldings.SpatialFolding.ConvexBoundary
