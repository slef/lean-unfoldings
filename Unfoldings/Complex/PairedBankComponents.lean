module

public import Unfoldings.Complex.CutSeamGraph
public import Unfoldings.Complex.BoundaryCycles
public import Unfoldings.Topology.GraphForestMap
public import Unfoldings.Topology.GraphReachability

/-!
# The two banks of a forest cut belong to the same boundary component

Every bank has an alternate boundary path. Project it to the primal cut graph.
A forest edge is a bridge, so that path must use the other bank of the same
seam. Thus both banks occur in one actual boundary-graph component.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)

theorem oppositeBanks_reaches (forest : (C.cutSeamGraph retain).IsAcyclic)
    (bank : C.BoundaryBank retain) :
    (C.boundaryGraph retain).graph.Reaches ((C.boundaryGraph retain).left bank)
      ((C.boundaryGraph retain).left (C.oppositeBank retain closed bank)) := by
  let G := C.boundaryGraph retain
  obtain ⟨u, v, detour, cycle⟩ := C.boundaryGraph_bank_liesOnCycle retain bank
  obtain ⟨other, member, different, same_seam⟩ :=
    cycle.exists_other_edge_of_map_to_forest (C.boundaryOriginalVertex retain)
      (C.bankCutSeam retain closed) (fun p _ => C.cutSeamGraph_preserves_vertex retain closed p)
      (fun {_ _ _} link => C.cutSeamGraph_preserves_link retain closed link) forest
  have paired : other = C.oppositeBank retain closed bank := by
    rcases (C.bankCutSeam_fiber retain closed other bank).mp same_seam with same | opposite
    · exact (different same).elim
    · exact opposite
  subst other
  have own_link : G.graph.IsLink bank (G.left bank) (G.right bank) := Or.inl ⟨rfl, rfl⟩
  have other_link : G.graph.IsLink (C.oppositeBank retain closed bank)
      (G.left (C.oppositeBank retain closed bank))
      (G.right (C.oppositeBank retain closed bank)) := Or.inl ⟨rfl, rfl⟩
  have source : G.graph.Reaches (G.left bank) u := by
    rcases cycle.isLink.left_eq_or_eq own_link with rfl | rfl
    · exact Graph.Reaches.refl own_link.left_mem
    · exact Graph.Reaches.of_isLink own_link
  exact source.trans (cycle.isPath.isWalk.reaches_mem_walkVertices
    (Graph.mem_walkVertices_of_mem_covered ⟨_, member, other_link.inc_left⟩))

theorem boundaryEnd_reaches_bank_left (p : C.BoundaryEnd retain) :
    (C.boundaryGraph retain).graph.Reaches (C.boundaryEndAsVertex retain p)
      ((C.boundaryGraph retain).left (C.boundaryEndEquiv retain p).1) := by
  let G := C.boundaryGraph retain
  let bank := (C.boundaryEndEquiv retain p).1
  have canonical : G.graph.IsLink bank (G.left bank) (G.right bank) := Or.inl ⟨rfl, rfl⟩
  rcases (C.boundaryGraph_bank_link retain p).left_eq_or_eq canonical with same | same
  · rw [same]
    exact Graph.Reaches.refl canonical.left_mem
  · rw [same]
    exact Graph.Reaches.of_isLink canonical.symm

theorem boundaryEnds_reaches_of_same_cutSeam (forest : (C.cutSeamGraph retain).IsAcyclic)
    (p q : C.BoundaryEnd retain)
    (same_seam : C.bankCutSeam retain closed (C.boundaryEndEquiv retain p).1 =
      C.bankCutSeam retain closed (C.boundaryEndEquiv retain q).1) :
    (C.boundaryGraph retain).graph.Reaches (C.boundaryEndAsVertex retain p)
      (C.boundaryEndAsVertex retain q) := by
  let G := C.boundaryGraph retain
  have banks : G.graph.Reaches (G.left (C.boundaryEndEquiv retain p).1)
      (G.left (C.boundaryEndEquiv retain q).1) := by
    rcases (C.bankCutSeam_fiber retain closed _ _).mp same_seam with same | opposite
    · rw [same]
      exact Graph.Reaches.refl (Set.mem_univ _)
    · rw [opposite]
      exact (C.oppositeBanks_reaches retain closed forest _).symm
  exact (C.boundaryEnd_reaches_bank_left retain p).trans
    (banks.trans (C.boundaryEnd_reaches_bank_left retain q).symm)

end Unfoldings.TriangleComplex
