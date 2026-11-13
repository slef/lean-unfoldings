module

public import Unfoldings.Topology.EscapeRays
public import Unfoldings.Topology.CompactJordanDisk
public import Schoenflies.JordanClosed

/-! A single Jordan curve in the frontier determines a regular compact planar patch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- A closed proper planar set with nonempty interior has a frontier point outside
any prescribed countable exceptional set. -/
theorem exists_frontier_not_mem_countable {S V : Set Plane} (closed : IsClosed S)
    (inside : (interior S).Nonempty) (outside : Sᶜ.Nonempty) (countable : V.Countable) :
    ∃ p ∈ frontier S, p ∉ V := by
  have dimension : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have connected := countable.isConnected_compl_of_one_lt_rank dimension
  by_contra none
  have boundary : frontier S ⊆ V := by
    intro p hp
    by_contra omitted
    exact none ⟨p, hp, omitted⟩
  have avoids : Disjoint Vᶜ (frontier S) :=
    Set.disjoint_left.mpr (fun _ omitted frontier => omitted (boundary frontier))
  have alternative := subset_interior_or_compl_of_avoids_frontier closed
    connected.isPreconnected avoids
  obtain ⟨a, omitted_a, interior_a⟩ := (countable.dense_compl ℝ).exists_mem_open
    isOpen_interior inside
  obtain ⟨b, omitted_b, outside_b⟩ := (countable.dense_compl ℝ).exists_mem_open
    closed.isOpen_compl outside
  rcases alternative with first | last
  · exact outside_b (interior_subset (first omitted_b))
  · exact last omitted_a (interior_subset interior_a)

/-- A compact planar set with connected interior and complement, equal to the closure of its
interior, is the closed Jordan domain of any Jordan curve contained in its frontier. -/
theorem eq_closure_inside_of_Jordan_frontier_subset {S J : Set Plane}
    (compact : IsCompact S) (regular : closure (interior S) = S)
    (connected_interior : IsConnected (interior S)) (connected_compl : IsConnected Sᶜ)
    (jordan : Schoenflies.IsJordanCurve J) (boundary : J ⊆ frontier S) :
    S = closure (Schoenflies.inside J) := by
  have separation := Schoenflies.jordan_curve_theorem jordan
  have filled : Schoenflies.inside J ⊆ S :=
    inside_subset_of_isConnected_compl compact connected_compl
      (boundary.trans compact.isClosed.frontier_subset)
  have filled_interior : Schoenflies.inside J ⊆ interior S :=
    separation.isOpen_inside.subset_interior_iff.mpr filled
  obtain ⟨p, inside⟩ := separation.isConnected_inside.nonempty
  have avoids : interior S ⊆ Jᶜ := by
    intro x hx hj
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hx (boundary hj)
  have contained : interior S ⊆ Schoenflies.inside J := by
    have components := connected_interior.isPreconnected.subset_connectedComponentIn
      (filled_interior inside) avoids
    rw [separation.connectedComponentIn_eq_inside inside] at components
    exact components
  exact Set.Subset.antisymm
    (by rw [← regular]; exact closure_mono contained)
    (closure_minimal filled compact.isClosed)

/-- A Jordan subcurve in the frontier is already the entire frontier under the connected
interior and no-holes hypotheses. This excludes all additional branches and boundary pinches. -/
theorem frontier_eq_of_Jordan_frontier_subset {S J : Set Plane}
    (compact : IsCompact S) (regular : closure (interior S) = S)
    (connected_interior : IsConnected (interior S)) (connected_compl : IsConnected Sᶜ)
    (jordan : Schoenflies.IsJordanCurve J) (boundary : J ⊆ frontier S) : frontier S = J := by
  have equality := eq_closure_inside_of_Jordan_frontier_subset compact regular
    connected_interior connected_compl jordan boundary
  apply Set.Subset.antisymm _ boundary
  rw [equality]
  exact frontier_closure_subset.trans
    (Schoenflies.jordan_curve_theorem jordan).frontier_inside.subset

/-- The same hypotheses construct an actual homeomorphism to the closed unit disk. -/
theorem exists_diskHomeomorph_of_Jordan_frontier_subset {S J : Set Plane}
    (compact : IsCompact S) (regular : closure (interior S) = S)
    (connected_interior : IsConnected (interior S)) (connected_compl : IsConnected Sᶜ)
    (jordan : Schoenflies.IsJordanCurve J) (boundary : J ⊆ frontier S) :
    Nonempty (S ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  apply exists_diskHomeomorph_of_compact_Jordan_frontier compact connected_interior.nonempty
  rw [frontier_eq_of_Jordan_frontier_subset compact regular connected_interior connected_compl
    jordan boundary]
  exact jordan

end Unfoldings.PlanarTopology
