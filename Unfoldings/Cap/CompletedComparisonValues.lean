module

public import Unfoldings.Cap.CompletedComparisonChains
public import Unfoldings.Cap.CompletedBankFaceValues

/-! Comparison-bank points are actual face values or chords between copies of one vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small D)

theorem entranceComparisonChain_original_point (i : FiveSector) (w : C.Vertex Set.univ)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    (B.entranceComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s =
      B.sectorFrame i (N.parentEntrancePoint D (N.completedBankChain w j) (1 - (s : ℝ))) := by
  rw [entranceComparisonChain, PolygonalChain.interleavedSegments_original_point]
  simp only [parentEntrancePoint, AffineMap.lineMap_apply_module, map_sub, map_smul,
    zero_smul, one_smul, sub_zero]
  module

theorem exitComparisonChain_original_point (i : FiveSector) (w : C.Vertex Set.univ)
    (origin : Plane) (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    (B.exitComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s =
      B.sectorFrame i (N.parentExitPoint D (N.completedBankChain w j) (1 - (s : ℝ))) := by
  rw [exitComparisonChain, PolygonalChain.interleavedSegments_original_point]
  simp only [parentExitPoint, AffineMap.lineMap_apply_module, map_sub, map_smul,
    zero_smul, one_smul, sub_zero]
  module

variable (i : FiveSector) (w : C.Vertex Set.univ)
  (target : Fin (N.completedContour.length + 1))
  (original : C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w)

include original

/-- Each straight entrance gap joins two containing-face copies of exactly the same
physical child vertex, even when the initial copy is chosen arbitrarily. -/
theorem entranceComparisonChain_gap_face_values
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    let p := K.projectedVertex (N.completedBankChain w j).val
    ∃ f g : Face, p ∈ (K.projectedTriangle f).carrier ∧ p ∈ (K.projectedTriangle g).carrier ∧
      (B.entranceComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point
          ⟨2 * j.val, by omega⟩ s =
          B.sectorFrame i (AffineMap.lineMap (D.projectedPlacement K f p)
            (D.projectedPlacement K g p) (s : ℝ)) := by
  obtain ⟨a, vertex, previous⟩ := N.completedBankChain_predecessor_copy D (B.sectorFrame i)
    w target original (fun e => N.parentEntrancePoint D e 0)
    (fun e => (N.parentBankOpening D e).enter)
    (N.parentEntrancePoint_parent_index D) (fun e => (N.parentBankOpening D e).entrance_vertex) j
  let e := N.completedBankChain w j
  let boundary := N.completedContour.cycle.point a
  have face := K.projected_bank_segment_mem_face boundary (s := 0) ⟨le_rfl, zero_le_one⟩
  rw [AffineMap.lineMap_apply_zero, vertex] at face
  have value := D.projectedPlacement_boundary_vertex K boundary
  rw [vertex] at value
  have named := N.parentEntrancePoint_eq_projectedPlacement D e 1
  rw [AffineMap.lineMap_apply_one] at named
  have named_face := (N.parent_bank_points_mem_faces D e (s := 1) ⟨zero_le_one, le_rfl⟩).1
  rw [AffineMap.lineMap_apply_one] at named_face
  refine ⟨boundary.val.1.1, (N.parentBankOpening D e).entranceFace, face, named_face, ?_⟩
  rw [entranceComparisonChain, PolygonalChain.interleavedSegments_gap_point, previous]
  change AffineMap.lineMap (B.sectorFrame i (D.boundaryPosition boundary))
    (B.sectorFrame i (N.parentEntrancePoint D e 1)) (s : ℝ) = _
  rw [← value, named]
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul]
  rfl

/-- Each exit gap likewise stays between two actual face copies of its physical vertex. -/
theorem exitComparisonChain_gap_face_values
    (j : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s : unitInterval) :
    let p := K.projectedVertex (N.completedBankChain w j).val
    ∃ f g : Face, p ∈ (K.projectedTriangle f).carrier ∧ p ∈ (K.projectedTriangle g).carrier ∧
      (B.exitComparisonChain i w
        (D.boundaryPosition (N.completedContour.cycle.point target))).point
          ⟨2 * j.val, by omega⟩ s =
          B.sectorFrame i (AffineMap.lineMap (D.projectedPlacement K f p)
            (D.projectedPlacement K g p) (s : ℝ)) := by
  obtain ⟨a, vertex, previous⟩ := N.completedBankChain_predecessor_copy D (B.sectorFrame i)
    w target original (fun e => N.parentExitPoint D e 0)
    (fun e => finRotate (N.completedContour.length + 1) (N.parentBankOpening D e).leave)
    (N.parentExitPoint_parent_index D) (fun e => (N.parentBankOpening D e).exit_next_vertex) j
  let e := N.completedBankChain w j
  let boundary := N.completedContour.cycle.point a
  have face := K.projected_bank_segment_mem_face boundary (s := 0) ⟨le_rfl, zero_le_one⟩
  rw [AffineMap.lineMap_apply_zero, vertex] at face
  have value := D.projectedPlacement_boundary_vertex K boundary
  rw [vertex] at value
  have named := N.parentExitPoint_eq_projectedPlacement D e 1
  rw [AffineMap.lineMap_apply_one] at named
  have named_face := (N.parent_bank_points_mem_faces D e (s := 1) ⟨zero_le_one, le_rfl⟩).2
  rw [AffineMap.lineMap_apply_one] at named_face
  refine ⟨boundary.val.1.1, (N.parentBankOpening D e).exitFace, face, named_face, ?_⟩
  rw [exitComparisonChain, PolygonalChain.interleavedSegments_gap_point, previous]
  change AffineMap.lineMap (B.sectorFrame i (D.boundaryPosition boundary))
    (B.sectorFrame i (N.parentExitPoint D e 1)) (s : ℝ) = _
  rw [← value, named]
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul]
  rfl

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
