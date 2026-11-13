module

public import Unfoldings.Topology.JordanBoundarySubset

/-! A filled Jordan subcurve determines a connected regular planar patch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- A Jordan curve has a point outside any prescribed countable exceptional set. -/
theorem exists_Jordan_point_not_mem_countable {J V : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (countable : V.Countable) :
    ∃ p ∈ J, p ∉ V := by
  by_contra none
  have subset : J ⊆ V := by
    intro p hp
    by_contra omitted
    exact none ⟨p, hp, omitted⟩
  obtain ⟨curve, loop, image⟩ := jordan
  have maps : Set.MapsTo curve (Set.Ico (0 : ℝ) 1) J := by
    intro t ht
    rw [← image]
    exact ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩
  have parameters := maps.countable_of_injOn loop.injOn (countable.mono subset)
  obtain ⟨t, omitted, inside⟩ := (parameters.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (Set.nonempty_Ioo.mpr (show (0 : ℝ) < 1 by norm_num))
  exact omitted ⟨inside.1.le, inside.2⟩

/-- If the inside of a Jordan boundary subcurve is filled, connectedness of the patch's
interior leaves no room outside that curve. -/
theorem eq_closure_inside_of_filled_Jordan_frontier_subset {S J : Set Plane}
    (compact : IsCompact S) (regular : closure (interior S) = S)
    (connected : IsConnected (interior S)) (jordan : Schoenflies.IsJordanCurve J)
    (boundary : J ⊆ frontier S) (filled : Schoenflies.inside J ⊆ S) :
    S = closure (Schoenflies.inside J) := by
  have separation := Schoenflies.jordan_curve_theorem jordan
  have filled_interior : Schoenflies.inside J ⊆ interior S :=
    separation.isOpen_inside.subset_interior_iff.mpr filled
  obtain ⟨p, inside⟩ := separation.isConnected_inside.nonempty
  have avoids : interior S ⊆ Jᶜ := by
    intro x hx hj
    exact Set.disjoint_left.mp disjoint_interior_frontier hx (boundary hj)
  have contained : interior S ⊆ Schoenflies.inside J := by
    have components := connected.isPreconnected.subset_connectedComponentIn
      (filled_interior inside) avoids
    rw [separation.connectedComponentIn_eq_inside inside] at components
    exact components
  exact Set.Subset.antisymm
    (by rw [← regular]; exact closure_mono contained)
    (closure_minimal filled compact.isClosed)

/-- A filled Jordan subcurve is the whole frontier of a regular compact patch with connected
interior. In particular no boundary vertex can pinch two parts of the patch together. -/
theorem frontier_eq_of_filled_Jordan_frontier_subset {S J : Set Plane}
    (compact : IsCompact S) (regular : closure (interior S) = S)
    (connected : IsConnected (interior S)) (jordan : Schoenflies.IsJordanCurve J)
    (boundary : J ⊆ frontier S) (filled : Schoenflies.inside J ⊆ S) : frontier S = J := by
  have equality := eq_closure_inside_of_filled_Jordan_frontier_subset compact regular
    connected jordan boundary filled
  apply Set.Subset.antisymm _ boundary
  rw [equality]
  exact frontier_closure_subset.trans
    (Schoenflies.jordan_curve_theorem jordan).frontier_inside.subset

end Unfoldings.PlanarTopology
