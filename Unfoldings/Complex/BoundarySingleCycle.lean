module

public import Unfoldings.Complex.BoundaryConnectivity

/-! Tree cuts on closed complexes have one actual boundary cycle covering every bank end. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

theorem boundaryCycle_visited_of_vertex_eq {n : ℕ}
    (cycle : (C.boundarySystem retain).Chain n)
    (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)
    {p q : C.BoundaryEnd retain}
    (same : C.boundaryEndAsVertex retain p = C.boundaryEndAsVertex retain q)
    (visited : cycle.Visited q) : cycle.Visited p := by
  rcases (C.boundaryEnd_vertex_eq_iff retain p q).mp (congrArg Subtype.val same) with rfl | rfl
  · exact visited
  · have start : C.boundaryMate retain cycle.first = C.boundaryTurn retain cycle.last := by
      rw [← closes, C.boundaryMate_involutive]
    exact cycle.visited_mate (Or.inl start) (Or.inl closes) visited

theorem boundaryCycle_covers_of_connected {n : ℕ}
    (cycle : (C.boundarySystem retain).Chain n)
    (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)
    (connected : (C.boundaryGraph retain).adjacencyGraph.Connected) :
    ∀ p, cycle.Visited p := by
  let G := C.boundaryGraph retain
  let P (v : C.BoundaryVertex retain) :=
    ∃ p : C.BoundaryEnd retain, C.boundaryEndAsVertex retain p = v ∧ cycle.Visited p
  have step {bank : C.BoundaryBank retain} {u v : C.BoundaryVertex retain}
      (link : G.graph.IsLink bank u v) (initial : P u) : P v := by
    obtain ⟨p, same, visited⟩ := initial
    rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · let first := (C.boundaryEndEquiv retain).symm (bank, false)
      have first_visited : cycle.Visited first :=
        C.boundaryCycle_visited_of_vertex_eq retain cycle closes same.symm visited
      refine ⟨C.boundaryTurn retain first, ?_, cycle.visited_turn first_visited⟩
      simp only [first, boundaryTurn, Equiv.apply_symm_apply, Bool.not_false]
      rfl
    · let first := (C.boundaryEndEquiv retain).symm (bank, true)
      have first_visited : cycle.Visited first :=
        C.boundaryCycle_visited_of_vertex_eq retain cycle closes same.symm visited
      refine ⟨C.boundaryTurn retain first, ?_, cycle.visited_turn first_visited⟩
      simp only [first, boundaryTurn, Equiv.apply_symm_apply, Bool.not_true]
      rfl
  intro p
  have reachable := G.graph_reaches_iff_adjacency.mpr
    (connected.preconnected (C.boundaryEndAsVertex retain cycle.first)
      (C.boundaryEndAsVertex retain p))
  obtain ⟨edges, walk⟩ := reachable
  have target : P (C.boundaryEndAsVertex retain p) :=
    walk.propagate P @step ⟨cycle.first, rfl, cycle.visited_first⟩
  obtain ⟨q, same, visited⟩ := target
  exact C.boundaryCycle_visited_of_vertex_eq retain cycle closes same.symm visited

variable (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)

include closed in
theorem exists_boundaryCycle_cover (forest : (C.cutSeamGraph retain).IsAcyclic)
    (connected : (C.cutSeamGraph retain).Connected) :
    ∃ n, ∃ cycle : (C.boundarySystem retain).Chain n,
      C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first ∧
        ∀ p, cycle.Visited p := by
  obtain ⟨v, member⟩ := connected.1
  obtain ⟨s, _side, _equal⟩ := member
  let p := (C.boundaryEndEquiv retain).symm (C.cutBank retain s false, false)
  obtain ⟨n, cycle, _first, closes⟩ := C.exists_boundaryCycle retain p
  exact ⟨n, cycle, closes, C.boundaryCycle_covers_of_connected retain cycle closes
    (C.boundaryGraph_connected_of_cutTree retain closed forest connected)⟩

end Unfoldings.TriangleComplex
