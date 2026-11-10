module

public import Unfoldings.Topology.SelectedForest

/-! Actual selected edge names at a childless nonroot vertex. -/

@[expose] public section

namespace Unfoldings.AscendingParents.EdgeSelection

variable {V E : Type*} {P : AscendingParents V} {G : Graph V E} (S : P.EdgeSelection G)

/-- At a childless nonroot, the unique selected incident edge is its own parent edge. -/
theorem edge_eq_at_childless {v w : V} (nonroot : v ∉ P.roots)
    (childless : ∀ u ∉ P.roots, P.parent u ≠ v) {e : E} (link : S.graph.IsLink e v w) :
    e = S.edge ⟨v, nonroot⟩ := by
  obtain ⟨u, named, endpoints⟩ := link
  rcases endpoints with ⟨same, _⟩ | ⟨same, _⟩
  · have vertices : (⟨v, nonroot⟩ : {x : V // x ∉ P.roots}) = u := Subtype.ext same
    rw [vertices]
    exact named.symm
  · exact (childless u.val u.property same.symm).elim

end Unfoldings.AscendingParents.EdgeSelection

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

/-- A finite nonempty set of nonroots has a childless vertex, by minimum potential. -/
theorem exists_childless_nonroot (nonempty : ∃ v, v ∉ P.roots) :
    ∃ v, v ∉ P.roots ∧ ∀ u ∉ P.roots, P.parent u ≠ v := by
  classical
  let := Fintype.ofFinite V
  let vertices := Finset.univ.filter (fun v : V => v ∉ P.roots)
  have present : vertices.Nonempty := by
    obtain ⟨v, hv⟩ := nonempty
    exact ⟨v, by simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv⟩
  obtain ⟨v, member, minimal⟩ := vertices.exists_min_image P.height present
  refine ⟨v, (Finset.mem_filter.mp member).2, fun u nonroot equal => ?_⟩
  have lower := minimal u (by
    simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact nonroot)
  have greater := P.ascending u nonroot
  rw [equal] at greater
  exact not_lt_of_ge lower greater

end Unfoldings.AscendingParents
