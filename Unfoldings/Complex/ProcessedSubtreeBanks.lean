module

public import Unfoldings.Complex.ProcessedCutBoundary
public import Unfoldings.Complex.SelectedSubtreeBoundary
public import Unfoldings.Complex.BoundaryContourRegions
public import Unfoldings.Topology.CyclicRegion

/-! Every processed original subtree has exactly two named current parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier) (roots : P.roots = C.relativeCutRoots Set.univ)

/-- The original parent seam is a genuine current cut once its selector has been processed. -/
def processedParentCut (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ frontier.processed) :
    C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ :=
  ⟨S.edge ⟨vertex, nonroot⟩, Set.mem_univ _,
    (C.not_mem_processedParentRetain_iff S frontier _).mpr ⟨⟨vertex, nonroot⟩, processed, rfl⟩⟩

include roots in
/-- Exactly the two original parent banks cross the current descendant separator.
Unprocessed descendants are allowed to remain curved in the interior. -/
theorem processed_subtree_crossing_iff (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ frontier.processed)
    (bank : C.BoundaryBank (C.processedParentRetain S frontier)) :
    C.BoundaryRegionCrossing
      (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex) bank ↔
      ∃ side, bank = C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
        (C.processedParentCut S frontier vertex nonroot processed) side := by
  let retain := C.processedParentRetain S frontier
  rcases C.relativeBank_cases retain Set.univ bank with old | ⟨s, side, rfl⟩
  · have first : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph retain).left bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_left (Set.subset_univ _) bank old
    have last : C.relativeBoundaryVertex (Set.subset_univ _)
        ((C.boundaryGraph retain).right bank) ∈ P.roots :=
      roots.symm ▸ C.relativeBoundaryVertex_old_right (Set.subset_univ _) bank old
    have no_crossing : ¬ C.BoundaryRegionCrossing
        (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex) bank := by
      rintro (⟨inside, _⟩ | ⟨inside, _⟩)
      · exact P.descendant_nonroot nonroot inside first
      · exact P.descendant_nonroot nonroot inside last
    have no_parent : ¬ ∃ side, bank = C.relativeCutBank retain Set.univ
        (C.processedParentCut S frontier vertex nonroot processed) side := by
      rintro ⟨side, rfl⟩
      exact C.relativeCutBank_not_old (C.processedParentCut S frontier vertex nonroot processed)
        side old
    exact iff_of_false no_crossing no_parent
  · have selected := C.processedCut_to_selection_link S frontier
      (C.relativeCutGraph_bank_link (Set.subset_univ _) s side)
    have crossing := S.crosses_descendants_iff nonroot selected
    change C.BoundaryRegionCrossing
      (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex)
      (C.relativeCutBank retain Set.univ s side) ↔ s.val = S.edge ⟨vertex, nonroot⟩ at crossing
    rw [crossing]
    constructor
    · intro same
      have seams : s = C.processedParentCut S frontier vertex nonroot processed := Subtype.ext same
      exact ⟨side, congrArg (fun t => C.relativeCutBank retain Set.univ t side) seams⟩
    · rintro ⟨other, equal⟩
      exact congrArg
        (fun p : C.RelativeCutSeam retain Set.univ × Bool => p.1.val)
        (C.relativeCutBank_injective retain Set.univ
          (a₁ := (s, side))
          (a₂ := (C.processedParentCut S frontier vertex nonroot processed, other)) equal)

/-- The current subtree separator has exactly two distinctly named original banks. -/
def processedSubtreeCrossingEquiv (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ frontier.processed) :
    Bool ≃ {bank : C.BoundaryBank (C.processedParentRetain S frontier) //
      C.BoundaryRegionCrossing
        (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex) bank} :=
  Equiv.ofBijective (fun side =>
    ⟨C.relativeCutBank (C.processedParentRetain S frontier) Set.univ
        (C.processedParentCut S frontier vertex nonroot processed) side,
      (C.processed_subtree_crossing_iff S frontier roots vertex nonroot processed _).mpr
        ⟨side, rfl⟩⟩) ⟨by
      intro a b same
      exact congrArg Prod.snd
        (C.relativeCutBank_injective _ _ (a₁ := (_, a)) (a₂ := (_, b))
          (congrArg Subtype.val same)), by
      intro bank
      obtain ⟨side, named⟩ :=
        (C.processed_subtree_crossing_iff S frontier roots vertex nonroot processed bank.val).mp
          bank.property
      exact ⟨side, Subtype.ext named.symm⟩⟩

variable (Q : C.BoundaryContour (C.processedParentRetain S frontier))

/-- Actual original descendant membership at a current boundary-contour vertex. -/
def ProcessedSubtreeBoundaryInside (vertex : C.Vertex Set.univ) (i : Fin (Q.length + 1)) : Prop :=
  P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex (C.processedParentRetain S frontier) (Q.cycle.point i))) vertex

/-- The two current contour transitions retain both distinct original bank labels. -/
def processedSubtreeBoundaryExitEquiv (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ frontier.processed) :
    Bool ≃ {i : Fin (Q.length + 1) //
      (C.ProcessedSubtreeBoundaryInside S frontier Q vertex i ∧
        ¬ C.ProcessedSubtreeBoundaryInside S frontier Q vertex (finRotate (Q.length + 1) i)) ∨
      (C.ProcessedSubtreeBoundaryInside S frontier Q vertex (finRotate (Q.length + 1) i) ∧
        ¬ C.ProcessedSubtreeBoundaryInside S frontier Q vertex i)} :=
  (C.processedSubtreeCrossingEquiv S frontier roots vertex nonroot processed).trans
    (((C.boundaryCycleBankEquiv (C.processedParentRetain S frontier) Q.cycle Q.covers).subtypeEquiv
      (fun i => (C.boundaryRegionCrossing_iff Q
        (fun w => P.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) vertex) i).symm)).symm)

include roots in
/-- One current original parent bank enters the processed subtree and the other leaves it.
This holds before fresh interior curvature is removed and requires no global development. -/
theorem exists_oriented_processed_subtree_exits (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (processed : vertex ∈ frontier.processed) :
    ∃ enter leave : Fin (Q.length + 1), enter ≠ leave ∧
      (¬ C.ProcessedSubtreeBoundaryInside S frontier Q vertex enter ∧
        C.ProcessedSubtreeBoundaryInside S frontier Q vertex (finRotate (Q.length + 1) enter)) ∧
      (C.ProcessedSubtreeBoundaryInside S frontier Q vertex leave ∧
        ¬ C.ProcessedSubtreeBoundaryInside S frontier Q vertex (finRotate (Q.length + 1) leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave →
        (C.ProcessedSubtreeBoundaryInside S frontier Q vertex (finRotate (Q.length + 1) i) ↔
          C.ProcessedSubtreeBoundaryInside S frontier Q vertex i) := by
  let exits := C.processedSubtreeBoundaryExitEquiv S frontier roots Q vertex nonroot processed
  let a := (exits false).val
  let b := (exits true).val
  have different : a ≠ b := by
    intro same
    have flags : false = true := exits.injective (Subtype.ext same)
    cases flags
  apply exists_oriented_two_exits (finRotate (Q.length + 1))
    (C.ProcessedSubtreeBoundaryInside S frontier Q vertex) a b different
  intro i
  constructor
  · intro changes
    obtain ⟨side, same⟩ := exits.surjective ⟨i, changes⟩
    cases side
    · exact Or.inl (congrArg Subtype.val same).symm
    · exact Or.inr (congrArg Subtype.val same).symm
  · rintro (rfl | rfl)
    · exact (exits false).property
    · exact (exits true).property

end Unfoldings.TriangleComplex
