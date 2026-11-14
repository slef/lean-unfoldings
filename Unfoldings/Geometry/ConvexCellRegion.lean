module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Connected.Basic

/-! A regular closed region selects actual cells whenever cell interiors avoid its frontier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCellRegion

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {I : Type*}
  (cells : I → Set E) (region : Set E)

/-- Selection is defined by actual interiors, rather than assumed boundary incidence data. -/
def selected : Set I := {i | (interior (cells i) ∩ interior region).Nonempty}

theorem cell_regular_closed (i : I) (closed : IsClosed (cells i))
    (convex : Convex ℝ (cells i)) (full : (interior (cells i)).Nonempty) :
    closure (interior (cells i)) = cells i := by
  rw [convex.closure_interior_eq_closure_of_nonempty_interior full, closed.closure_eq]

theorem interior_subset_of_selected (i : I) (convex : Convex ℝ (cells i))
    (avoids : Disjoint (interior (cells i)) (frontier region))
    (member : i ∈ selected cells region) : interior (cells i) ⊆ interior region := by
  apply convex.interior.isPreconnected.subset_of_closure_inter_subset isOpen_interior member
  intro x incident
  by_contra outside
  have boundary : x ∈ frontier region := by
    rw [frontier]
    exact ⟨closure_mono interior_subset incident.1, outside⟩
  exact Set.disjoint_left.mp avoids incident.2 boundary

/-- At an interior region point, every incident full-dimensional cell is selected. -/
theorem selected_of_incident_interior (i : I) (closed : IsClosed (cells i))
    (convex : Convex ℝ (cells i)) (full : (interior (cells i)).Nonempty)
    {x : E} (inside : x ∈ interior region) (incident : x ∈ cells i) :
    i ∈ selected cells region := by
  by_contra none
  have excluded : interior (cells i) ⊆ (interior region)ᶜ := by
    intro y hy hr
    exact none ⟨y, hy, hr⟩
  have closure_excluded := closure_minimal excluded isOpen_interior.isClosed_compl
  rw [cell_regular_closed cells i closed convex full] at closure_excluded
  exact closure_excluded incident inside

theorem cell_subset_of_selected (i : I) (closed_region : IsClosed region)
    (closed : IsClosed (cells i)) (convex : Convex ℝ (cells i))
    (full : (interior (cells i)).Nonempty)
    (avoids : Disjoint (interior (cells i)) (frontier region))
    (member : i ∈ selected cells region) : cells i ⊆ region := by
  rw [← cell_regular_closed cells i closed convex full]
  exact closure_minimal
    ((interior_subset_of_selected cells region i convex avoids member).trans interior_subset)
    closed_region

variable [Finite I]

/-- The exact region is the union of its constructed selected closed cells. -/
theorem eq_union_selected_cells (closed_region : IsClosed region)
    (regular : closure (interior region) = region)
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty)
    (covered : interior region ⊆ ⋃ i, cells i)
    (avoids : ∀ i, Disjoint (interior (cells i)) (frontier region)) :
    region = ⋃ i ∈ selected cells region, cells i := by
  have closed_union : IsClosed (⋃ i ∈ selected cells region, cells i) :=
    (Set.toFinite (selected cells region)).isClosed_biUnion (fun i _ => closed i)
  apply Set.Subset.antisymm
  · have inside : interior region ⊆ ⋃ i ∈ selected cells region, cells i := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (covered hx)
      exact Set.mem_iUnion₂.mpr ⟨i,
        selected_of_incident_interior cells region i (closed i) (convex i) (full i) hx hi, hi⟩
    simpa only [regular] using closure_minimal inside closed_union
  · intro x hx
    obtain ⟨i, selected, hi⟩ := Set.mem_iUnion₂.mp hx
    exact cell_subset_of_selected cells region i closed_region (closed i) (convex i)
      (full i) (avoids i) selected hi

end Unfoldings.ConvexCellRegion
