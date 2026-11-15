module

public import Unfoldings.Cap.SplitBankSector
public import Unfoldings.Cone.ComplementaryModelCompletion

/-! Complete the actual retained split-bank tangent fan by its complementary geometric sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {retain : Set C.Seam} (w z : C.Vertex retain) (distinct : w ≠ z)
  (same : C.vertexForgetCuts (Set.subset_univ retain) z =
    C.vertexForgetCuts (Set.subset_univ retain) w)
  (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w))

include K z distinct same internal in
/-- The actual retained tangent fan, glued only along its two original ordered banks to
the complementary geometric sector, has the whole-plane metric. Either piece may be reentrant.
This is a local tangent-model completion, retaining the original corner labels and placement. -/
theorem exists_split_bank_completed_plane :
    ∃ n, ∃ c : (C.linkSystem retain w).Chain n,
    ∃ _covers : ∀ p, c.Visited p,
    ∃ _start : C.linkMate retain w c.first = c.first,
    ∃ _finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last,
    ∃ E : C.TangentFan retain w ≃ᵢ PolygonalPoint (closedAngularSector (C.totalAngle retain w)),
      (E (C.tangentOrigin retain w)).val = 0 ∧
      ∃ F : ComplementaryModelCompletion E ≃ᵢ ℂ,
        (∀ x : (C.linkAngularFan retain w c).Surface,
          F (complementaryModelOriginal E (C.angularToTangent retain w c x)) =
            (C.linkAngularFan retain w c).develop x) ∧
        (∀ y : PolygonalPoint (complementarySector (C.totalAngle retain w)),
          F (complementaryModelGap E y) = y.val) := by
  obtain ⟨n, c, covers, start, finish, E, center, placement, _positive, _small⟩ :=
    K.exists_split_bank_sector_isometry w z distinct same internal
  let positive := C.totalAngle_pos retain w
  let small := K.split_bank_totalAngle_lt_full w z distinct same internal
  refine ⟨n, c, covers, start, finish, E, center,
    complementaryModelPlaneIsometryEquiv E positive small, ?_, ?_⟩
  · intro x
    rw [complementaryModelPlane_original]
    exact placement x
  · exact complementaryModelPlane_gap E positive small

end Unfoldings.ConvexCap
