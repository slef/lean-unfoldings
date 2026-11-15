module

public import Unfoldings.Complex.CurrentBankSelectors

/-! The reference original surface cut only along one named ancestor path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- Cut only original parent seams on the path from this vertex to its original rim root. -/
def ancestorPathRetain (base : C.Vertex Set.univ) : Set C.Seam :=
  {s | ∀ e : {v : C.Vertex Set.univ // v ∉ P.roots}, P.Ancestor base e.val → S.edge e ≠ s}

/-- The full selected cut refines the reference path cut. -/
theorem selectedRetain_subset_ancestorPathRetain (base : C.Vertex Set.univ) :
    C.selectedRetain S ⊆ C.ancestorPathRetain S base :=
  fun _ kept e _ same => kept ⟨e, same⟩

/-- If the base is processed, all reference path cuts are already present in the current cut. -/
theorem processedRetain_subset_ancestorPathRetain (frontier : P.ParentFrontier)
    (base : C.Vertex Set.univ) (processed : base ∈ frontier.processed) :
    C.processedParentRetain S frontier ⊆ C.ancestorPathRetain S base := by
  intro s kept e ancestor
  obtain ⟨n, at_vertex⟩ := ancestor
  exact kept e (at_vertex ▸ frontier.iterate_mem_of_mem processed n)

/-- The reference cut removes exactly the named original seams of ancestor selectors. -/
theorem parent_edge_cut_ancestorPath_iff (base : C.Vertex Set.univ)
    (e : {v : C.Vertex Set.univ // v ∉ P.roots}) :
    S.edge e ∉ C.ancestorPathRetain S base ↔ P.Ancestor base e.val := by
  classical
  constructor
  · intro cut
    by_contra outside
    apply cut
    intro f ancestor same
    have equal := congrArg Subtype.val (S.edge_injective same)
    exact outside (equal ▸ ancestor)
  · exact fun ancestor kept => kept e ancestor rfl

/-- A named original parent bank survives in the reference cut exactly on the ancestor path. -/
theorem selected_parent_bank_ancestorPath_iff (base vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) side) :
    C.IsBoundaryEdge (C.ancestorPathRetain S base) (C.germEdge p.val) ↔ P.Ancestor base vertex := by
  have raw := congrArg (fun bank : C.BoundaryBank (C.selectedRetain S) => bank.val) named
  change C.germEdge p.val = C.seamSide (S.edge ⟨vertex, nonroot⟩) side at raw
  rw [raw]
  have boundary : C.IsBoundaryEdge (C.ancestorPathRetain S base)
      (C.seamSide (S.edge ⟨vertex, nonroot⟩) side) ↔
        S.edge ⟨vertex, nonroot⟩ ∉ C.ancestorPathRetain S base := by
    cases side
    · exact C.isBoundaryEdge_left_iff _ _
    · exact C.isBoundaryEdge_right_iff _ _
  exact boundary.trans (C.parent_edge_cut_ancestorPath_iff S base ⟨vertex, nonroot⟩)

end Unfoldings.TriangleComplex
