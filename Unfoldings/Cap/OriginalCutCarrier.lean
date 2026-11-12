module

public import Unfoldings.Cap.ExtendedCutCurvature
public import Unfoldings.Cap.ProjectedDevelopedMap

/-! The selected original forest segments are exactly the actual closed original seam cut set. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem isClosed_projectedCutSet (retain : Set C.Seam) : IsClosed (K.projectedCutSet retain) :=
  isClosed_iUnion_of_finite fun s => isClosed_iUnion_of_finite fun _ =>
    ((K.projectedTriangle (C.left s).face).compact_edge (C.left s).edge).isClosed

namespace SectorForest

variable {K} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

theorem projectedCutCarrier_eq_projectedCutSet :
    M.projectedCutCarrier = K.projectedCutSet M.retain := by
  ext p
  constructor
  · intro member
    obtain ⟨e, member⟩ := Set.mem_iUnion.mp member
    refine Set.mem_iUnion.mpr ⟨M.selection.edge e, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · intro kept
      exact kept ⟨e, rfl⟩
    · exact (M.parent_segment_eq_original_seam e).subset member
  · intro member
    obtain ⟨s, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨cut, member⟩ := Set.mem_iUnion.mp member
    have chosen : s ∈ Set.range M.selection.edge := Classical.not_not.mp cut
    obtain ⟨e, rfl⟩ := chosen
    exact Set.mem_iUnion.mpr ⟨e, (M.parent_segment_eq_original_seam e).symm.subset member⟩

end SectorForest
end Unfoldings.ConvexCap
