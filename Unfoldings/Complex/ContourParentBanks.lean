module

public import Unfoldings.Complex.SupportedSubtreeContour
public import Unfoldings.Complex.ParentBankEndpoints

/-! Original contour entrances and exits fix both actual oriented copies of every parent bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Literal contour tags for both sides of one original selected parent seam. -/
structure ContourParentInterval (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots) where
  enter : Fin (Q.length + 1)
  leave : Fin (Q.length + 1)
  side : Bool
  ordered : enter.val < leave.val
  subtree : ∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
    enter.val < i.val ∧ i.val ≤ leave.val
  entry_named : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point enter)).1 =
    C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S vertex nonroot) side
  exit_named : (C.boundaryEndEquiv (C.selectedRetain S) (Q.cycle.point leave)).1 =
    C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S vertex nonroot) (!side)

variable (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

/-- The original contour derives the actual two-sided interval; no side label is supplied. -/
def contourParentInterval (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots) :
    C.ContourParentInterval S Q vertex nonroot := Classical.choice (by
  obtain ⟨enter, leave, side, ordered, subtree, entry_named, exit_named⟩ :=
    C.exists_named_linear_subtree_interval_of_boundary_roots S roots Q starts vertex nonroot
  exact ⟨⟨enter, leave, side, ordered, subtree, entry_named, exit_named⟩⟩)

/-- Both actual bank copies are oriented from the original child to its parent.
The first is the literal contour exit and the second the reversed contour entrance. -/
def contourParentBank (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots) (side : Bool) :
    C.BoundaryEnd (C.selectedRetain S) :=
  let data := C.contourParentInterval S Q roots starts vertex nonroot
  if side then C.boundaryTurn _ (Q.cycle.point data.enter) else Q.cycle.point data.leave

/-- The contour exit begins at the child and ends at its parent. -/
theorem contourParentInterval_exit_original (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    let data := C.contourParentInterval S Q roots starts vertex nonroot
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (Q.cycle.point data.leave)) = vertex ∧
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (Q.cycle.point data.leave))) = P.parent vertex := by
  let data := C.contourParentInterval S Q roots starts vertex nonroot
  exact C.selected_parent_bank_leaves S vertex nonroot (Q.cycle.point data.leave) (!data.side)
    data.exit_named ((data.subtree data.leave).mpr ⟨data.ordered, le_rfl⟩)

/-- The literal entrance has the opposite original endpoint order. -/
theorem contourParentInterval_entry_original (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    let data := C.contourParentInterval S Q roots starts vertex nonroot
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (Q.cycle.point data.enter)) = P.parent vertex ∧
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (Q.cycle.point data.enter))) = vertex := by
  let data := C.contourParentInterval S Q roots starts vertex nonroot
  apply C.selected_parent_bank_enters S vertex nonroot (Q.cycle.point data.enter) data.side
    data.entry_named
  intro inside
  exact (lt_irrefl _ ((data.subtree data.enter).mp inside).1)

/-- Every chosen side starts at exactly the named original parent-bank child. -/
theorem contourParentBank_start (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (side : Bool) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _
        (C.contourParentBank S Q roots starts vertex nonroot side)) = vertex := by
  cases side
  · exact (C.contourParentInterval_exit_original S Q roots starts vertex nonroot).1
  · exact (C.contourParentInterval_entry_original S Q roots starts vertex nonroot).2

/-- Both original sides retain the actual parent as their true far endpoint. -/
theorem contourParentBank_finish (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (side : Bool) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _
        (C.contourParentBank S Q roots starts vertex nonroot side))) = P.parent vertex := by
  cases side
  · exact (C.contourParentInterval_exit_original S Q roots starts vertex nonroot).2
  · change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (C.boundaryTurn _ (Q.cycle.point
        (C.contourParentInterval S Q roots starts vertex nonroot).enter)))) = _
    rw [C.boundaryTurn_involutive]
    exact (C.contourParentInterval_entry_original S Q roots starts vertex nonroot).1

/-- The two oriented bank tags are distinct actual copies of the original cut. -/
theorem contourParentBank_distinct (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots) :
    C.contourParentBank S Q roots starts vertex nonroot false ≠
      C.contourParentBank S Q roots starts vertex nonroot true :=
  Q.cycle.disjoint (C.contourParentInterval S Q roots starts vertex nonroot).leave
    (C.contourParentInterval S Q roots starts vertex nonroot).enter

/-- A rootward original contour occurrence is exactly the exit-side bank.
Original endpoints alone would permit both oriented sides; the literal contour tag fixes one. -/
theorem contourParentBank_eq_of_contour (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (i : Fin (Q.length + 1))
    (first : C.contourOriginalVertex S Q i = vertex)
    (last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ (C.boundaryTurn _ (Q.cycle.point i))) = P.parent vertex) :
    Q.cycle.point i = C.contourParentBank S Q roots starts vertex nonroot false := by
  let data := C.contourParentInterval S Q roots starts vertex nonroot
  let p := Q.cycle.point i
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) p).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with rim | ⟨s, side, named⟩
  · let original : C.BoundaryEnd Set.univ := ⟨p.val, rim⟩
    have rooted := roots (C.boundaryEndAsVertex Set.univ original).property
    exact (nonroot (first ▸ rooted)).elim
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    rcases C.selected_parent_bank_endpoints S e.val e.property p side named with forward | reverse
    · have e_same : e.val = vertex := forward.1.symm.trans first
      have named_vertex : bank = C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S vertex nonroot) side := by
        change bank = C.relativeCutBank (C.selectedRetain S) Set.univ
          (C.selectedParentCut S e.val e.property) side at named
        simpa only [e_same] using named
      rcases C.named_parent_bank_index_eq S Q vertex nonroot data.enter data.leave i data.side
        side data.entry_named data.exit_named named_vertex with entry | exit
      · have inside : P.Ancestor (C.contourOriginalVertex S Q i) vertex :=
          first ▸ P.ancestor_refl vertex
        have bounds := (data.subtree i).mp inside
        exact (lt_irrefl _ (entry ▸ bounds.1)).elim
      · exact congrArg Q.cycle.point exit
    · have desired : P.parent vertex = e.val := last.symm.trans reverse.2
      have up := P.ascending vertex nonroot
      rw [desired] at up
      have down := P.ascending e.val e.property
      rw [← reverse.1] at down
      change P.height e.val < P.height (C.contourOriginalVertex S Q i) at down
      rw [first] at down
      exact (lt_asymm up down).elim

end Unfoldings.TriangleComplex
