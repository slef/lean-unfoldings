module

public import Unfoldings.Complex.ClosedBanks
public import Unfoldings.Complex.GermEndpoints

/-!
# The actual primal cut multigraph of a closed triangle complex

Each cut seam is one edge, with its two original endpoint classes. The vertex
set contains exactly incident vertices. Actual boundary-bank links project to
these original links; the two banks of a seam remain distinct in the domain.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

def cutSeamVertex (s : C.CutSeam retain) (endSide : Bool) : C.Vertex Set.univ :=
  C.vertexOfCorner Set.univ (C.germOfEndpoint (C.left s.val) endSide).1

def cutSeamGraph : Graph (C.Vertex Set.univ) (C.CutSeam retain) where
  vertexSet := {v | ∃ s b, v = C.cutSeamVertex retain s b}
  edgeSet := Set.univ
  IsLink s u v :=
    (u = C.cutSeamVertex retain s false ∧ v = C.cutSeamVertex retain s true) ∨
      (u = C.cutSeamVertex retain s true ∧ v = C.cutSeamVertex retain s false)
  isLink_symm := by
    intro s _
    constructor
    intro u v h
    exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro s u v w z h k
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp
  edge_mem_iff_exists_isLink s :=
    ⟨fun _ => ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    intro s u v link
    rcases link with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨s, false, rfl⟩
    · exact ⟨s, true, rfl⟩

def boundaryOriginalVertex (p : C.BoundaryVertex retain) : C.Vertex Set.univ :=
  C.vertexForgetCuts (Set.subset_univ retain) p.val

theorem cutSeamGraph_side_link (s : C.CutSeam retain) (side : Bool) :
    (C.cutSeamGraph retain).IsLink s
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s.val side) false).1)
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s.val side) true).1) := by
  cases side
  · exact Or.inl ⟨rfl, rfl⟩
  · have endpoints (b : Bool) :
        C.vertexOfCorner Set.univ (C.germOfEndpoint (C.right s.val) b).1 =
          C.cutSeamVertex retain s (C.acrossEndpoint s.val true b) := by
      exact (show C.GermCrosses Set.univ
        (C.germOfEndpoint (C.right s.val) b)
        (C.germOfEndpoint (C.left s.val) (C.acrossEndpoint s.val true b))
        from ⟨s.val, Set.mem_univ _, true, b, rfl, rfl⟩).vertex_eq
    change (C.cutSeamGraph retain).IsLink s
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.right s.val) false).1)
      (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.right s.val) true).1)
    have swaps : C.acrossEndpoint s.val true true = !(C.acrossEndpoint s.val true false) := by
      simpa only [Bool.not_false] using C.acrossEndpoint_not s.val true false
    rw [endpoints false, endpoints true, swaps]
    cases C.acrossEndpoint s.val true false
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

variable (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)

theorem cutSeamGraph_bank_link (bank : C.BoundaryBank retain) :
    (C.cutSeamGraph retain).IsLink (C.bankCutSeam retain closed bank)
      (C.boundaryOriginalVertex retain ((C.boundaryGraph retain).left bank))
      (C.boundaryOriginalVertex retain ((C.boundaryGraph retain).right bank)) := by
  obtain ⟨⟨s, side⟩, rfl⟩ := (C.cutBankEquiv retain closed).surjective bank
  rw [C.cutBankEquiv_apply, C.bankCutSeam_cutBank]
  exact C.cutSeamGraph_side_link retain s side

theorem cutSeamGraph_preserves_link {bank : C.BoundaryBank retain}
    {u v : C.BoundaryVertex retain} (link : (C.boundaryGraph retain).graph.IsLink bank u v) :
    (C.cutSeamGraph retain).IsLink (C.bankCutSeam retain closed bank)
      (C.boundaryOriginalVertex retain u) (C.boundaryOriginalVertex retain v) := by
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact C.cutSeamGraph_bank_link retain closed bank
  · exact (C.cutSeamGraph_bank_link retain closed bank).symm

include closed in
theorem cutSeamGraph_preserves_vertex (v : C.BoundaryVertex retain) :
    C.boundaryOriginalVertex retain v ∈ (C.cutSeamGraph retain).vertexSet := by
  obtain ⟨bank, w, link⟩ := C.boundaryGraph_vertex_incident retain v
  exact (C.cutSeamGraph_preserves_link retain closed link).left_mem

end Unfoldings.TriangleComplex
