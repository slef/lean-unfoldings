module

public import Unfoldings.Geometry.Edge
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Perfect

/-! Every neighborhood in a genuine closed edge contains a nonvertex point. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem edgePerfectSpace (T : Triangle) (e : Fin 3) : PerfectSpace (T.Edge e) := by
  let : ConnectedSpace (T.Edge e) := isConnected_iff_connectedSpace.mp
    ((convex_segment (T.vertex e) (T.vertex (next e))).isConnected
      ⟨T.vertex e, left_mem_segment ℝ _ _⟩)
  let : Nontrivial (T.Edge e) :=
    ⟨⟨⟨T.vertex e, left_mem_segment ℝ _ _⟩, ⟨T.vertex (next e), right_mem_segment ℝ _ _⟩,
      fun equal => T.edge_endpoints_ne e (congrArg Subtype.val equal)⟩⟩
  infer_instance

theorem exists_nonvertex_in_edge_neighborhood (T : Triangle) (e : Fin 3)
    (x : T.Edge e) {U : Set (T.Edge e)} (open_U : IsOpen U) (inside : x ∈ U) :
    ∃ y ∈ U, ¬ T.IsVertex y := by
  let := T.edgePerfectSpace e
  have finite : {y : T.Edge e | T.IsVertex y}.Finite :=
    (Set.finite_range T.vertex).of_injOn (f := fun y : T.Edge e => y.val)
      (fun _ hy => hy) Subtype.val_injective.injOn
  by_contra no_point
  apply infinite_of_mem_nhds x (open_U.mem_nhds inside)
  apply finite.subset
  intro y hy
  by_contra not_vertex
  exact no_point ⟨y, hy, not_vertex⟩

end Unfoldings.Triangle
