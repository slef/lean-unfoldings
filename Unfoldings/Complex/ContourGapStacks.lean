module

public import Unfoldings.Complex.SupportedContourNeighbors
public import Mathlib.Data.Finset.Sort

/-! Actual positive fresh contour sources give the ordered gap stack on each parent edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Positive gaps are indexed by their original fresh source steps, not by supplied events. -/
abbrev PositiveContourSource := {j : Fin Q.length //
  C.contourOriginalVertex S Q j.castSucc ∉ (C.contourFrontier S Q j.castSucc).processed ∧
    0 < C.interiorAngularDefect Set.univ (C.contourOriginalVertex S Q j.castSucc)}

instance positiveContourSourceFintype : Fintype (C.PositiveContourSource S Q) :=
  Fintype.ofFinite _

/-- The actual original vertex charged by a positive fresh contour source. -/
def positiveContourVertex (source : C.PositiveContourSource S Q) : C.Vertex Set.univ :=
  C.contourOriginalVertex S Q source.val.castSucc

/-- Retain the original contour order of every actual positive fresh source. -/
def positiveContourSources : List (C.PositiveContourSource S Q) := Finset.univ.sort

/-- Every actual positive fresh source occurs once in this complete ordered list. -/
theorem mem_positiveContourSources (source : C.PositiveContourSource S Q) :
    source ∈ C.positiveContourSources S Q := by simp [positiveContourSources]

theorem positiveContourSources_nodup : (C.positiveContourSources S Q).Nodup :=
  Finset.sort_nodup _ _

open Classical in
/-- The gap stack over one original parent bank consists exactly of its descendant sources. -/
def contourEdgeGapStack (vertex : C.Vertex Set.univ) : List (C.PositiveContourSource S Q) :=
  (C.positiveContourSources S Q).filter (fun source =>
    P.Ancestor (C.positiveContourVertex S Q source) vertex)

/-- Membership is derived from the original parent forest, with no stack-assignment input. -/
theorem mem_contourEdgeGapStack (vertex : C.Vertex Set.univ)
    (source : C.PositiveContourSource S Q) :
    source ∈ C.contourEdgeGapStack S Q vertex ↔
      P.Ancestor (C.positiveContourVertex S Q source) vertex := by
  classical
  simp only [contourEdgeGapStack, List.mem_filter, decide_eq_true_eq,
    C.mem_positiveContourSources S Q source, true_and]

theorem contourEdgeGapStack_nodup (vertex : C.Vertex Set.univ) :
    (C.contourEdgeGapStack S Q vertex).Nodup :=
  (C.positiveContourSources_nodup S Q).filter _

/-- Each original edge keeps the actual strict source order, independently of tree branching. -/
theorem contourEdgeGapStack_ordered (vertex : C.Vertex Set.univ) :
    (C.contourEdgeGapStack S Q vertex).Pairwise
      (fun a b => a.val.val < b.val.val) := by
  change (C.contourEdgeGapStack S Q vertex).Pairwise (· < ·)
  exact (Finset.sortedLT_sort
    (Finset.univ : Finset (C.PositiveContourSource S Q))).pairwise.filter _

/-- Every gap touching a parent edge continues onto its next parent edge or root tail. -/
theorem contourEdgeGapStack_parent (vertex : C.Vertex Set.univ)
    (source : C.PositiveContourSource S Q)
    (member : source ∈ C.contourEdgeGapStack S Q vertex) :
    source ∈ C.contourEdgeGapStack S Q (P.parent vertex) :=
  (C.mem_contourEdgeGapStack S Q _ source).mpr
    (((C.mem_contourEdgeGapStack S Q vertex source).mp member).trans P (P.ancestor_parent vertex))

/-- At a root, the stack consists of exactly its original tree component's positive sources. -/
theorem mem_contourRootGapStack (root : C.Vertex Set.univ) (root_mem : root ∈ P.roots)
    (source : C.PositiveContourSource S Q) :
    source ∈ C.contourEdgeGapStack S Q root ↔
      P.root (C.positiveContourVertex S Q source) = root := by
  rw [C.mem_contourEdgeGapStack]
  constructor
  · intro ancestor
    exact P.ancestor_root_unique (P.ancestor_root _) ancestor (P.root_mem _) root_mem
  · intro same
    exact same ▸ P.ancestor_root _

/-- Reading away from the untouched exit bank meets the latest inserted gap first. -/
def contourSavedGapStack (vertex : C.Vertex Set.univ) : List (C.PositiveContourSource S Q) :=
  (C.contourEdgeGapStack S Q vertex).reverse

/-- Reversing the attachment order preserves exactly the original descendant sources. -/
theorem mem_contourSavedGapStack (vertex : C.Vertex Set.univ)
    (source : C.PositiveContourSource S Q) :
    source ∈ C.contourSavedGapStack S Q vertex ↔
      P.Ancestor (C.positiveContourVertex S Q source) vertex := by
  rw [contourSavedGapStack, List.mem_reverse, C.mem_contourEdgeGapStack]

theorem contourSavedGapStack_nodup (vertex : C.Vertex Set.univ) :
    (C.contourSavedGapStack S Q vertex).Nodup :=
  List.nodup_reverse.mpr (C.contourEdgeGapStack_nodup S Q vertex)

variable (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include roots starts in
/-- Earlier positive sources have already been processed at every later source step. -/
theorem positiveContourSource_passed (a b : C.PositiveContourSource S Q) (before : a.val < b.val) :
    C.positiveContourVertex S Q a ∈ (C.contourFrontier S Q b.val.castSucc).processed :=
  (C.rim_contour_processed_iff_of_boundary_roots S roots Q starts b.val.castSucc _).mpr
    (Or.inr ⟨a.val.castSucc, before, rfl⟩)

include roots starts in
/-- The ordered positive gap family charges each original vertex at most once. -/
theorem positiveContourVertex_injective : Function.Injective (C.positiveContourVertex S Q) := by
  intro a b same
  by_cases equal : a.val = b.val
  · exact Subtype.ext equal
  · rcases lt_or_gt_of_ne equal with before | after
    · apply False.elim
      apply b.property.1
      change C.positiveContourVertex S Q b ∈ (C.contourFrontier S Q b.val.castSucc).processed
      rw [← same]
      exact C.positiveContourSource_passed S Q roots starts a b before
    · apply False.elim
      apply a.property.1
      change C.positiveContourVertex S Q a ∈ (C.contourFrontier S Q a.val.castSucc).processed
      rw [same]
      exact C.positiveContourSource_passed S Q roots starts b a after

end Unfoldings.TriangleComplex
