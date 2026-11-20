module

public import Unfoldings.Topology.ClosedJordanDomain

/-! A Jordan cycle in a planar cellular skeleton encloses complete cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- Cells whose interiors meet the bounded side of a Jordan cycle in the
skeleton fill that side, including its boundary. The skeleton may contain
other edges and vertices inside the cycle. -/
theorem closedJordanDomain_eq_iUnion_cells {I : Type*} [Finite I] {J skeleton : Set Plane}
    (cycle : Schoenflies.IsJordanCurve J) (sub_skeleton : J ⊆ skeleton)
    (thin : interior skeleton = ∅) (cell : I → Set Plane)
    (closed : ∀ i, IsClosed (cell i))
    (regular : ∀ i, closure (interior (cell i)) = cell i)
    (connected : ∀ i, IsPreconnected (interior (cell i)))
    (apart : ∀ i, Disjoint (interior (cell i)) skeleton)
    (boundary : ∀ i, frontier (cell i) ⊆ skeleton)
    (coverage : Schoenflies.inside J ⊆ ⋃ i, cell i) :
    closedJordanDomain J =
      ⋃ i : {i : I // (interior (cell i) ∩ Schoenflies.inside J).Nonempty}, cell i := by
  let A := {i : I // (interior (cell i) ∩ Schoenflies.inside J).Nonempty}
  let filled := ⋃ i : A, cell i
  let separation := Schoenflies.jordan_curve_theorem cycle
  have filled_closed : IsClosed filled := isClosed_iUnion_of_finite (fun i : A => closed i)
  have includes_cell (i : A) : cell i ⊆ closedJordanDomain J := by
    obtain ⟨x, xi, inside⟩ := i.property
    have avoids : interior (cell i) ⊆ Jᶜ := fun y hy hJ =>
      Set.disjoint_left.mp (apart i) hy (sub_skeleton hJ)
    have hc := (connected i).subset_connectedComponentIn xi avoids
    rw [separation.connectedComponentIn_eq_inside inside] at hc
    rw [← regular i]
    exact closure_mono hc
  have includes_inside : Schoenflies.inside J ⊆ filled := by
    intro x x_in
    by_contra x_out
    let U := Schoenflies.inside J ∩ filledᶜ
    have U_open : IsOpen U := separation.isOpen_inside.inter filled_closed.isOpen_compl
    have U_ne : U.Nonempty := ⟨x, x_in, x_out⟩
    have not_subset : ¬U ⊆ skeleton := by
      intro h
      have h' := interior_maximal h U_open
      rw [thin] at h'
      exact (Set.not_nonempty_empty) (U_ne.mono h')
    obtain ⟨y, hy, outside⟩ := Set.not_subset.mp not_subset
    obtain ⟨i, yi⟩ := Set.mem_iUnion.mp (coverage hy.1)
    have interior_y : y ∈ interior (cell i) := by
      by_contra not_in
      have on_frontier : y ∈ frontier (cell i) := by
        rw [(closed i).frontier_eq]
        exact ⟨yi, not_in⟩
      exact outside (boundary i on_frontier)
    exact hy.2 (Set.mem_iUnion.mpr ⟨⟨i, y, interior_y, hy.1⟩, yi⟩)
  exact (closure_minimal includes_inside filled_closed).antisymm
    (Set.iUnion_subset includes_cell)

/-- If a convex region contains the cycle, every enclosed cell lies entirely
in the same convex region. -/
theorem cell_subset_convex_of_inside_cycle {I : Type*} [Finite I]
    {J skeleton K : Set Plane} (cycle : Schoenflies.IsJordanCurve J)
    (sub_skeleton : J ⊆ skeleton) (thin : interior skeleton = ∅)
    (cell : I → Set Plane) (closed : ∀ i, IsClosed (cell i))
    (regular : ∀ i, closure (interior (cell i)) = cell i)
    (connected : ∀ i, IsPreconnected (interior (cell i)))
    (apart : ∀ i, Disjoint (interior (cell i)) skeleton)
    (boundary : ∀ i, frontier (cell i) ⊆ skeleton)
    (coverage : Schoenflies.inside J ⊆ ⋃ i, cell i)
    (compact : IsCompact K) (convex : Convex ℝ K) (contains : J ⊆ K)
    (i : I) (inside : (interior (cell i) ∩ Schoenflies.inside J).Nonempty) :
    cell i ⊆ K := by
  have fill := closedJordanDomain_subset_convex cycle compact convex contains
  rw [closedJordanDomain_eq_iUnion_cells cycle sub_skeleton thin cell closed regular connected
    apart boundary coverage] at fill
  exact (Set.subset_iUnion _ ⟨i, inside⟩).trans fill

end Unfoldings.PlanarTopology
