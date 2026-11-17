module

public import Unfoldings.Geometry.SpatialEnvelopeDirectedBanks
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! Orient an actual fine bank in a prescribed segment's original parameter order. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance bankOrientationIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable {retain : Set T.pairedComplex.Seam}

/-- Endpoint membership in an original segment determines a strictly forward bank
orientation and retains every named contact copy. -/
theorem exists_forward_bank_of_segment_endpoints (p : T.pairedComplex.BoundaryEnd retain)
    (a b : Plane)
    (initial : Cap.horizontal (T.pairedFolding.boundaryPosition p) ∈ segment ℝ a b)
    (final : Cap.horizontal (T.pairedFolding.boundaryPosition
      (T.pairedComplex.boundaryTurn retain p)) ∈ segment ℝ a b)
    (u : unitInterval) :
    ∃ (q : T.pairedComplex.BoundaryEnd retain) (s t : unitInterval), s.val < t.val ∧
      Cap.horizontal (T.pairedFolding.boundaryPosition q) = AffineMap.lineMap a b s.val ∧
      Cap.horizontal (T.pairedFolding.boundaryPosition (T.pairedComplex.boundaryTurn retain q)) =
        AffineMap.lineMap a b t.val ∧
      ∃ v : unitInterval, T.pairedComplex.directedBoundaryPath q v =
        T.pairedComplex.directedBoundaryPath p u := by
  rw [segment_eq_image_lineMap] at initial final
  obtain ⟨s, hs, first⟩ := initial
  obtain ⟨t, ht, last⟩ := final
  have different : s ≠ t := by
    intro same
    exact T.horizontal_boundaryPosition_ne p
      (first.symm.trans ((congrArg (AffineMap.lineMap a b) same).trans last))
  rcases lt_or_gt_of_ne different with forward | backward
  · exact ⟨p, ⟨s, hs⟩, ⟨t, ht⟩, forward, first.symm, last.symm, u, rfl⟩
  · refine ⟨T.pairedComplex.boundaryTurn retain p, ⟨t, ht⟩, ⟨s, hs⟩, backward,
      last.symm, ?_, ?_⟩
    · rw [T.pairedComplex.boundaryTurn_involutive]
      exact first.symm
    · refine ⟨unitInterval.symm u, ?_⟩
      rw [T.pairedComplex.directedBoundaryPath_turn, unitInterval.symm_symm]

/-- A nonvertex actual bank contact occurs strictly between the bank's endpoints. -/
theorem directedBoundaryPath_time_interior (p : T.pairedComplex.BoundaryEnd retain)
    (u : unitInterval)
    (regular : ∀ v : T.pairedComplex.Vertex retain,
      T.pairedComplex.directedBoundaryPath p u ≠ T.pairedComplex.vertexPoint retain v) :
    u ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · apply lt_of_le_of_ne bot_le
    intro same
    subst u
    exact regular _ (T.pairedComplex.directedBoundaryPath_zero p)
  · apply lt_of_le_of_ne le_top
    intro same
    subst u
    exact regular _ (T.pairedComplex.directedBoundaryPath_one p)

end Unfoldings.SpatialEnvelope.Triangulation
