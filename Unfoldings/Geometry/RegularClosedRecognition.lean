module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.ClusterPt

/-! A regular closed region is identified by its frontier and one interior witness. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [TopologicalSpace E]

/-- Connected interior and exterior make one orientation witness sufficient to recognize
an actual regular closed region with the same nonempty boundary. -/
theorem eq_of_regular_closed_frontier_eq {s t : Set E}
    (regular_s : closure (interior s) = s) (regular_t : closure (interior t) = t)
    (inside_connected : IsPreconnected (interior s)) (outside_connected : IsPreconnected sᶜ)
    (boundary_nonempty : (frontier s).Nonempty) (boundary : frontier t = frontier s)
    (witness : (interior s ∩ interior t).Nonempty) : t = s := by
  have closed_s : IsClosed s := regular_s ▸ isClosed_closure
  have closed_t : IsClosed t := regular_t ▸ isClosed_closure
  have fill (U : Set E) (connected : IsPreconnected U) (avoids : Disjoint U (frontier t))
      (meets : (U ∩ interior t).Nonempty) : U ⊆ interior t := by
    apply connected.subset_of_closure_inter_subset isOpen_interior meets
    intro x member
    by_contra outside
    have incident : x ∈ frontier t := ⟨closure_mono interior_subset member.1, outside⟩
    exact Set.disjoint_left.mp avoids member.2 incident
  have inside_avoids : Disjoint (interior s) (frontier t) := by
    rw [boundary]
    exact Set.disjoint_left.mpr (fun _ inside incident => incident.2 inside)
  have inside_t : s ⊆ t := by
    rw [← regular_s]
    exact closure_minimal ((fill _ inside_connected inside_avoids witness).trans interior_subset)
      closed_t
  apply Set.Subset.antisymm _ inside_t
  intro x member
  by_contra outside
  have near_t : x ∈ closure (interior t) := by rwa [regular_t]
  have meets : (sᶜ ∩ interior t).Nonempty :=
    mem_closure_iff_nhds.mp near_t sᶜ (closed_s.isOpen_compl.mem_nhds outside)
  have outside_avoids : Disjoint sᶜ (frontier t) := by
    rw [boundary]
    exact Set.disjoint_left.mpr (fun _ absent incident =>
      absent (closed_s.closure_eq ▸ incident.1))
  have outside_t := fill _ outside_connected outside_avoids meets
  have whole : t = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases present : y ∈ s
    · exact inside_t present
    · exact interior_subset (outside_t present)
  rw [← boundary, whole, frontier_univ] at boundary_nonempty
  exact boundary_nonempty.ne_empty rfl

end Unfoldings
