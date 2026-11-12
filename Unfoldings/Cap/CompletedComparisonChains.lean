module

public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Cap.CompletedBankChainOrder
public import Unfoldings.Cap.CompletedExcursionStrictOrder
public import Unfoldings.Geometry.InterleavedSegments

/-! Actual outward bank paths completed by straight segments between the branch copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

/-- A predecessor endpoint is always an actual copy of the next edge's child vertex. -/
theorem completedBankChain_predecessor_copy {E : Type*} (frame : Plane → E)
    (w : C.Vertex Set.univ) (target : Fin (N.completedContour.length + 1))
    (original : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)
    (position : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots} → Plane)
    (index : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots} →
      Fin (N.completedContour.length + 1))
    (represented : ∀ e, position e = D.boundaryPosition (N.completedContour.cycle.point (index e)))
    (parent : ∀ e, C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point (index e))) =
        N.spanningCompletion.parents.parent e.val)
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    ∃ a : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point a)) =
          (N.completedBankChain w j).val ∧
      PolygonalChain.segmentPredecessor (frame (D.boundaryPosition
        (N.completedContour.cycle.point target)))
        (fun k => frame (position (N.completedBankChain w k))) j =
          frame (D.boundaryPosition (N.completedContour.cycle.point a)) := by
  by_cases zero : j.val = 0
  · refine ⟨target, ?_, ?_⟩
    · simpa only [completedBankChain, zero, Function.iterate_zero, id_eq] using original
    · simp only [PolygonalChain.segmentPredecessor, dite_eq_left zero]
  · let previous : Fin (N.spanningCompletion.parents.distanceToRoot w) := ⟨j.val - 1, by omega⟩
    refine ⟨index (N.completedBankChain w previous), ?_, ?_⟩
    · exact (parent _).trans (N.completedBankChain_parent w previous j (by
        change j.val = j.val - 1 + 1
        omega))
    · simp only [PolygonalChain.segmentPredecessor, dite_eq_right zero, represented, previous]

namespace FiveSectorFrameData

variable {N D} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

/-- The right comparison bank starts at the chosen actual branch copy. Each actual
outward entrance-bank edge is preceded by its straight gap, including the initial gap. -/
def entranceComparisonChain (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane) :
    PolygonalChain ℂ (2 * N.spanningCompletion.parents.distanceToRoot w) :=
  PolygonalChain.interleavedSegments (B.sectorFrame i origin)
    (fun j => B.sectorFrame i (N.parentEntrancePoint D (N.completedBankChain w j) 1))
    (fun j => B.sectorFrame i (N.parentEntrancePoint D (N.completedBankChain w j) 0))

/-- The left comparison bank has the same initial actual branch copy, and retains
every straight gap and outward exit-bank edge. It need not be radially monotone. -/
def exitComparisonChain (i : FiveSector) (w : C.Vertex Set.univ) (origin : Plane) :
    PolygonalChain ℂ (2 * N.spanningCompletion.parents.distanceToRoot w) :=
  PolygonalChain.interleavedSegments (B.sectorFrame i origin)
    (fun j => B.sectorFrame i (N.parentExitPoint D (N.completedBankChain w j) 1))
    (fun j => B.sectorFrame i (N.parentExitPoint D (N.completedBankChain w j) 0))

theorem entranceComparisonChain_original_edge (i : FiveSector) (w : C.Vertex Set.univ)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    (B.entranceComparisonChain i w origin).edge ⟨2 * j.val + 1, by omega⟩ =
      B.sectorFrame i (N.parentEntryVector D (N.completedBankChain w j)) := by
  rw [entranceComparisonChain, PolygonalChain.interleavedSegments_original_edge, ← map_sub]
  congr 1
  simp only [parentEntrancePoint, zero_smul, sub_zero, one_smul]
  abel

theorem exitComparisonChain_original_edge (i : FiveSector) (w : C.Vertex Set.univ)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    (B.exitComparisonChain i w origin).edge ⟨2 * j.val + 1, by omega⟩ =
      B.sectorFrame i (N.parentExitVector D (N.completedBankChain w j)) := by
  rw [exitComparisonChain, PolygonalChain.interleavedSegments_original_edge, ← map_sub]
  congr 1
  simp only [parentExitPoint, zero_smul, sub_zero, one_smul]
  abel

variable (i : FiveSector) (w : C.Vertex Set.univ)
  (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)

include original

theorem entranceComparisonChain_gap_copy
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    ∃ a : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point a)) =
          (N.completedBankChain w j).val ∧
      (B.entranceComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).edge
        ⟨2 * j.val, by omega⟩ =
          B.sectorFrame i (N.parentEntrancePoint D (N.completedBankChain w j) 1 -
            D.boundaryPosition (N.completedContour.cycle.point a)) := by
  obtain ⟨a, vertex, previous⟩ := N.completedBankChain_predecessor_copy D (B.sectorFrame i)
    w target original (fun e => N.parentEntrancePoint D e 0)
    (fun e => (N.parentBankOpening D e).enter)
    (N.parentEntrancePoint_parent_index D) (fun e => (N.parentBankOpening D e).entrance_vertex) j
  refine ⟨a, vertex, ?_⟩
  rw [entranceComparisonChain, PolygonalChain.interleavedSegments_gap_edge, previous, map_sub]

theorem exitComparisonChain_gap_copy
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
    ∃ a : Fin (N.completedContour.length + 1),
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point a)) =
          (N.completedBankChain w j).val ∧
      (B.exitComparisonChain i w (D.boundaryPosition (N.completedContour.cycle.point target))).edge
        ⟨2 * j.val, by omega⟩ =
          B.sectorFrame i (N.parentExitPoint D (N.completedBankChain w j) 1 -
            D.boundaryPosition (N.completedContour.cycle.point a)) := by
  obtain ⟨a, vertex, previous⟩ := N.completedBankChain_predecessor_copy D (B.sectorFrame i)
    w target original (fun e => N.parentExitPoint D e 0)
    (fun e => finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).leave)
    (N.parentExitPoint_parent_index D) (fun e => (N.parentBankOpening D e).exit_next_vertex) j
  refine ⟨a, vertex, ?_⟩
  rw [exitComparisonChain, PolygonalChain.interleavedSegments_gap_edge, previous, map_sub]

end FiveSectorFrameData
end Unfoldings.ConvexCap.RadialCutForest
