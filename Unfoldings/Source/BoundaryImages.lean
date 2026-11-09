module

public import Unfoldings.Source.CompletedPieces

/-!
# A finite rigid representation of every shortest-path source vector in every endpoint face

The finite compact-graph cover represents every completed point in one face.
An actual bounded seam route at its endpoint transports that pointwise
representation to any other original face copy, even when the endpoint is
cut or singular. This constructs a finite family for all shortest paths and
all endpoint face choices, retaining ties separately.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_finite_all_source_vectors :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ M : Set (Plane ≃ᵃⁱ[ℝ] Plane), M.Finite ∧ ∀ (p : SourcePath source)
        (f : Face) (x : C.Cell f), p.target = C.faceMap Set.univ f x →
          ∃ A ∈ M, R.coordinate p.path p.geodesic = A x.val := by
  let := P.metricSpace
  intro source R
  obtain ⟨M, finite, pieces⟩ := P.exists_finite_completed_face_pieces R
  let N := ⋃ A ∈ M, Set.range (C.boundedWordPlacement (N := Fintype.card Face) A)
  have finite_N : N.Finite := finite.biUnion
    (fun A _ => C.finite_boundedWordPlacements (Fintype.card Face) A)
  refine ⟨N, finite_N, ?_⟩
  intro p f x target
  let z := R.coordinateHomeomorph (P.sourcePathCoordinate_injective R) p
  obtain ⟨A, member, g, y, vector, projection⟩ := pieces z
  have y_target : C.faceMap Set.univ g y = p.target :=
    projection.symm.trans (R.projection_coordinateHomeomorph (P.sourcePathCoordinate_injective R) p)
  let a : C.PointFiber Set.univ p.target := ⟨⟨g, y⟩, y_target⟩
  let b : C.PointFiber Set.univ p.target := ⟨⟨f, x⟩, target.symm⟩
  obtain ⟨W, short⟩ := F.exists_short_pointSeamRoute Set.univ p.target a b
  let B := C.boundedWordPlacement A (W.code C short)
  have in_N : B ∈ N :=
    Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr ⟨member, W.code C short, rfl⟩⟩
  refine ⟨B, in_N, ?_⟩
  have command := W.code_agrees C short A
  exact vector.trans command.symm

end Unfoldings.SpatialFolding.ConvexBoundary
