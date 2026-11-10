module

public import Unfoldings.Complex.CutSeamGraph
public import Unfoldings.Topology.GraphRootExtension

/-!
# New cuts relative to an already cut surface

Only seams restored in the original surface and removed in the further cut
are edges of this multigraph. Existing bank edges are never counted as cuts.
Original boundary vertices are marked roots. We include them as isolated
vertices when no new cut meets them; these harmless rooted singleton components
make the outside-star construction uniform even for the empty cut.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (small large : Set C.Seam)

abbrev RelativeCutSeam := {s : C.Seam // s ∈ large ∧ s ∉ small}

def relativeCutBank (s : C.RelativeCutSeam small large) (side : Bool) : C.BoundaryBank small :=
  C.cutBank small ⟨s.val, s.property.2⟩ side

def relativeCutVertex (s : C.RelativeCutSeam small large) (side : Bool) : C.Vertex large :=
  C.vertexOfCorner large (C.germOfEndpoint (C.left s.val) side).1

def relativeCutRoots : Set (C.Vertex large) := {v | C.IsBoundaryVertex large v}

def relativeCutGraph : Graph (C.Vertex large) (C.RelativeCutSeam small large) where
  vertexSet := C.relativeCutRoots large ∪ {v | ∃ s b, v = C.relativeCutVertex small large s b}
  edgeSet := Set.univ
  IsLink s u v :=
    (u = C.relativeCutVertex small large s false ∧
      v = C.relativeCutVertex small large s true) ∨
    (u = C.relativeCutVertex small large s true ∧
      v = C.relativeCutVertex small large s false)
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
    · exact Or.inr ⟨s, false, rfl⟩
    · exact Or.inr ⟨s, true, rfl⟩

def relativeCutRootExtension :=
  (C.relativeCutGraph small large).rootExtension (C.relativeCutRoots large)

theorem relativeCutRootExtension_tree_iff :
    (C.relativeCutRootExtension small large).IsTree ↔
      (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large) :=
  (C.relativeCutGraph small large).rootExtension_isTree_iff _ (fun _ h => Or.inl h)

theorem relativeBank_cases (bank : C.BoundaryBank small) :
    C.IsBoundaryEdge large bank.val ∨
      ∃ s : C.RelativeCutSeam small large, ∃ side, bank = C.relativeCutBank small large s side := by
  by_cases old : C.IsBoundaryEdge large bank.val
  · exact Or.inl old
  · right
    obtain ⟨s, kept, incident⟩ := Classical.not_not.mp old
    have cut : s ∉ small := fun member => bank.property ⟨s, member, incident⟩
    refine ⟨⟨s, kept, cut⟩, ?_⟩
    rcases incident with first | last
    · exact ⟨false, Subtype.ext first⟩
    · exact ⟨true, Subtype.ext last⟩

theorem relativeCutBank_injective : Function.Injective
    (fun p : C.RelativeCutSeam small large × Bool => C.relativeCutBank small large p.1 p.2) := by
  intro p q equal
  have same := C.cutBank_injective small
    (a₁ := (⟨p.1.val, p.1.property.2⟩, p.2))
    (a₂ := (⟨q.1.val, q.1.property.2⟩, q.2)) equal
  have seams := congrArg (fun p : C.CutSeam small × Bool => p.1.val) same
  have sides := congrArg (fun p : C.CutSeam small × Bool => p.2) same
  exact Prod.ext (Subtype.ext seams) sides

variable {small large}

def relativeBoundaryVertex (inclusion : small ⊆ large) (p : C.BoundaryVertex small) :
    C.Vertex large := C.vertexForgetCuts inclusion p.val

theorem relativeCutGraph_bank_link (inclusion : small ⊆ large)
    (s : C.RelativeCutSeam small large) (side : Bool) :
    (C.relativeCutGraph small large).IsLink s
      (C.relativeBoundaryVertex inclusion
        ((C.boundaryGraph small).left (C.relativeCutBank small large s side)))
      (C.relativeBoundaryVertex inclusion
        ((C.boundaryGraph small).right (C.relativeCutBank small large s side))) := by
  cases side
  · exact Or.inl ⟨rfl, rfl⟩
  · have endpoints (b : Bool) :
        C.vertexOfCorner large (C.germOfEndpoint (C.right s.val) b).1 =
          C.relativeCutVertex small large s (C.acrossEndpoint s.val true b) := by
      exact (show C.GermCrosses large
        (C.germOfEndpoint (C.right s.val) b)
        (C.germOfEndpoint (C.left s.val) (C.acrossEndpoint s.val true b))
        from ⟨s.val, s.property.1, true, b, rfl, rfl⟩).vertex_eq
    change (C.relativeCutGraph small large).IsLink s
      (C.vertexOfCorner large (C.germOfEndpoint (C.right s.val) false).1)
      (C.vertexOfCorner large (C.germOfEndpoint (C.right s.val) true).1)
    have swaps : C.acrossEndpoint s.val true true = !(C.acrossEndpoint s.val true false) := by
      simpa only [Bool.not_false] using C.acrossEndpoint_not s.val true false
    rw [endpoints false, endpoints true, swaps]
    cases C.acrossEndpoint s.val true false
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

theorem relativeBoundaryVertex_old_left (inclusion : small ⊆ large)
    (bank : C.BoundaryBank small) (old : C.IsBoundaryEdge large bank.val) :
    C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).left bank) ∈
      C.relativeCutRoots large :=
  ⟨bank.val, old, Or.inl rfl⟩

theorem relativeBoundaryVertex_old_right (inclusion : small ⊆ large)
    (bank : C.BoundaryBank small) (old : C.IsBoundaryEdge large bank.val) :
    C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).right bank) ∈
      C.relativeCutRoots large :=
  ⟨bank.val, old, Or.inr rfl⟩

theorem relativeBoundaryVertex_member (inclusion : small ⊆ large) (p : C.BoundaryVertex small) :
    C.relativeBoundaryVertex inclusion p ∈ (C.relativeCutGraph small large).vertexSet := by
  obtain ⟨bank, w, link⟩ := C.boundaryGraph_vertex_incident small p
  rcases C.relativeBank_cases small large bank with old | ⟨s, side, rfl⟩
  · rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (C.relativeBoundaryVertex_old_left inclusion bank old)
    · exact Or.inl (C.relativeBoundaryVertex_old_right inclusion bank old)
  · rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (C.relativeCutGraph_bank_link inclusion s side).left_mem
    · exact (C.relativeCutGraph_bank_link inclusion s side).right_mem

end Unfoldings.TriangleComplex
