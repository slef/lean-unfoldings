module

public import Unfoldings.Complex.SupportedRootwardChain
public import Unfoldings.Cone.RootwardPathFanMetric

/-! Actual original rootward fan restoration permits unused isolated roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))
  (fresh : C.contourOriginalVertex S Q i ∉ (C.contourFrontier S Q i).processed)

include boundary_roots starts fresh in
/-- The original parent-path cut retains every actual upcoming rootward bank. -/
theorem rootward_bank_survives_ancestorPath_of_boundary_roots (j : C.RootwardBank S Q i) :
    C.IsBoundaryEdge (C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i)))
      (C.germEdge (Q.cycle.point j.val).val) := by
  have data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  obtain ⟨nonroot, side, named⟩ := C.future_current_bank_named_of_boundary_roots S boundary_roots
    Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  apply (C.selected_parent_bank_ancestorPath_iff S _ _ nonroot _ side named).mpr
  apply (P.ancestor_parent_iff (show C.contourOriginalVertex S Q i ≠
    C.contourOriginalVertex S Q j.val from fun same => fresh (same.symm ▸ data.2.1))).mp
  exact data.2.2.1



end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))
  (fresh : C.contourOriginalVertex S Q i ∉ (C.contourFrontier S Q i).processed)
  (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)

include F boundary_roots starts fresh in
/-- Both terminal banks of each actual rootward junction survive when all side cuts are
restored. This constructs the original one-sided reference fan from the actual current fan. -/
theorem rootward_path_fan_terminal_banks_of_boundary_roots (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let current := C.processedParentRetain S (C.contourFrontier S Q i)
    let reference := C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i))
    let p := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    C.IsBoundaryEdge reference (C.germEdge p.val) ∧
      C.IsBoundaryEdge reference (C.germEdge (C.boundaryMate current p).val) := by
  dsimp only
  refine ⟨C.rootward_bank_survives_ancestorPath_of_boundary_roots S boundary_roots Q starts i
    fresh k, ?_⟩
  have step := F.rootward_boundary_step_of_boundary_roots S boundary_roots Q starts i j k parent
  have mate := congrArg (C.boundaryMate (C.processedParentRetain S (C.contourFrontier S Q i))) step
  rw [C.boundaryMate_involutive] at mate
  rw [← mate]
  have same := congrArg (fun bank : C.BoundaryBank
    (C.processedParentRetain S (C.contourFrontier S Q i)) => bank.val)
    ((C.boundaryEnd_bank_eq_iff (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.boundaryTurn _ (C.survivingBoundaryEnd (Q.cycle.point j.val) j.property.2.1))
      (C.survivingBoundaryEnd (Q.cycle.point j.val) j.property.2.1)).mpr (Or.inr rfl))
  change C.germEdge _ = C.germEdge _ at same
  rw [same]
  exact C.rootward_bank_survives_ancestorPath_of_boundary_roots S boundary_roots Q starts i fresh j

include F boundary_roots starts fresh single in
/-- The whole local metric of the current rootward fan equals its original path-cut fan.
The comparison is canonical cut restoration on original faces, including the two banks. -/
theorem exists_rootward_path_fan_forgetChart_of_boundary_roots (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let frontier := C.contourFrontier S Q i
    let base := P.parent (C.contourOriginalVertex S Q i)
    let processed : base ∈ frontier.processed := by
      change P.parent (C.contourOriginalVertex S Q i) ∈ (C.contourFrontier S Q i).processed
      have member := (C.contourFrontier S Q i).contact_mem (C.contourOriginalVertex S Q i)
      simpa only [single, Function.iterate_one] using member
    Nonempty (MetricGluing.ForgetChart C.Cell
      (C.glue_mono (C.processedRetain_subset_ancestorPathRetain S frontier base processed))
      (C.cornerPoint (Q.cycle.point k.val).val.1)) := by
  dsimp only
  have parent_processed : P.parent (C.contourOriginalVertex S Q i) ∈
      (C.contourFrontier S Q i).processed := by
    have member := (C.contourFrontier S Q i).contact_mem (C.contourOriginalVertex S Q i)
    simpa only [single, Function.iterate_one] using member
  obtain ⟨first, last⟩ := F.rootward_path_fan_terminal_banks_of_boundary_roots S boundary_roots Q
    starts i fresh j k parent
  exact C.exists_boundary_fan_forgetChart
    (C.processedRetain_subset_ancestorPathRetain S (C.contourFrontier S Q i) _ parent_processed)
    (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1) first last


include F boundary_roots starts fresh single in
/-- Exact equality of the triangle corners in the actual current fan and its original
one-sided path reference. This is independent of any chosen planar development. -/
theorem rootward_path_fan_corners_iff_of_boundary_roots (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) (a : C.Corner) :
    let current := C.processedParentRetain S (C.contourFrontier S Q i)
    let reference := C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i))
    let p := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    C.vertexOfCorner reference a =
        C.vertexForgetCuts (C.rootwardPathInclusion S Q i single) (C.boundaryEndVertex current p) ↔
      C.vertexOfCorner current a = C.boundaryEndVertex current p := by
  obtain ⟨first, last⟩ := F.rootward_path_fan_terminal_banks_of_boundary_roots S boundary_roots Q
    starts i fresh j k parent
  exact C.boundary_fan_corners_iff (C.rootwardPathInclusion S Q i single)
    (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1) first last a

include F boundary_roots starts fresh single in
/-- The actual one-sided original fan has exactly the current fan's whole angle. -/
theorem rootward_path_fan_totalAngle_of_boundary_roots (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let current := C.processedParentRetain S (C.contourFrontier S Q i)
    let reference := C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i))
    let p := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    C.totalAngle reference
        (C.vertexForgetCuts (C.rootwardPathInclusion S Q i single)
          (C.boundaryEndVertex current p)) =
      C.totalAngle current (C.boundaryEndVertex current p) := by
  obtain ⟨first, last⟩ := F.rootward_path_fan_terminal_banks_of_boundary_roots S boundary_roots Q
    starts i fresh j k parent
  exact C.boundary_fan_totalAngle (C.rootwardPathInclusion S Q i single)
    (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1) first last


include F boundary_roots starts fresh single in
/-- Construct the actual intrinsic tangent-fan isometry to the original path-cut fan.
Every original supporting-wedge point is fixed, including reentrant fans. -/
theorem exists_rootward_path_fan_isometry_of_boundary_roots (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let current := C.processedParentRetain S (C.contourFrontier S Q i)
    let reference := C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i))
    let p := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    let vertex := C.boundaryEndVertex current p
    ∃ E : C.TangentFan current vertex ≃ᵢ
      C.TangentFan reference (C.vertexForgetCuts (C.rootwardPathInclusion S Q i single) vertex),
      ∀ (q : C.CornerAt current vertex) (x : C.TangentCell current vertex q),
        E (C.tangentFaceMap current vertex q x) =
          C.tangentFaceMap reference
            (C.vertexForgetCuts (C.rootwardPathInclusion S Q i single) vertex)
            (C.restoreCorner (C.rootwardPathInclusion S Q i single) q) x := by
  obtain ⟨first, last⟩ := F.rootward_path_fan_terminal_banks_of_boundary_roots S boundary_roots Q
    starts i fresh j k parent
  exact C.exists_boundaryFanRestorationIsometry (C.rootwardPathInclusion S Q i single)
    (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1) first last


end Unfoldings.SpatialFolding
