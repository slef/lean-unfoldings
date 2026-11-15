module

public import Unfoldings.Complex.RestoredContourExcursion
public import Unfoldings.Complex.SurvivingBoundaryBanks

/-! Skipping restored original contour excursions gives the actual current boundary successor. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  {retain : Set C.Seam} (inclusion : C.selectedRetain S ⊆ retain)

include F roots inclusion in
/-- After deleting a restored excursion, the two surviving banks are adjacent in the actual
current cut boundary. Their meeting is derived intrinsically; no current endpoint equality
or successor premise is assumed. -/
theorem pruned_contour_boundary_step (region : Fin (Q.length + 1) → Prop)
    (a b : Fin (Q.length + 1)) (different : a ≠ b)
    (enters : ¬ region a ∧ region (finRotate (Q.length + 1) a))
    (leaves : region b ∧ ¬ region (finRotate (Q.length + 1) b))
    (stable : ∀ i, i ≠ a → i ≠ b →
      (region (finRotate (Q.length + 1) i) ↔ region i))
    (same_original : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) a))) =
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex (C.selectedRetain S)
          (Q.cycle.point (finRotate (Q.length + 1) b))))
    (restored : ∀ i, region i →
      ¬ C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point i).val))
    (incoming : C.IsBoundaryEdge retain (C.germEdge (Q.cycle.point a).val))
    (outgoing : C.IsBoundaryEdge retain
      (C.germEdge (Q.cycle.point (finRotate (Q.length + 1) b)).val)) :
    C.boundaryMate retain
        (C.boundaryTurn retain (C.survivingBoundaryEnd (Q.cycle.point a) incoming)) =
      C.survivingBoundaryEnd (Q.cycle.point (finRotate (Q.length + 1) b)) outgoing := by
  have equal := F.restored_contour_excursion_endpoints_eq S roots Q inclusion region a b
    different enters leaves stable same_original restored
  let p := C.boundaryTurn retain (C.survivingBoundaryEnd (Q.cycle.point a) incoming)
  let q := C.survivingBoundaryEnd (Q.cycle.point (finRotate (Q.length + 1) b)) outgoing
  have next := congrArg Subtype.val
    (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes a)
  change C.boundaryEndVertex (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point a)) =
    C.boundaryEndVertex (C.selectedRetain S)
      (Q.cycle.point (finRotate (Q.length + 1) a)) at next
  have same : C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := by
    change C.vertexForgetCuts inclusion
      (C.boundaryEndVertex (C.selectedRetain S)
        (Q.cycle.point (finRotate (Q.length + 1) b))) =
      C.vertexForgetCuts inclusion
        (C.boundaryEndVertex (C.selectedRetain S)
          (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point a)))
    rw [next]
    exact equal
  have distinct : q ≠ p := by
    intro same_end
    apply Q.cycle.disjoint (finRotate (Q.length + 1) b) a
    apply Subtype.ext
    exact congrArg (fun e : C.BoundaryEnd retain => e.val) same_end
  exact ((C.exists_unique_other_boundaryEnd retain p).unique ⟨distinct, same⟩
    (C.boundaryMate_spec retain p)).symm

end Unfoldings.SpatialFolding
