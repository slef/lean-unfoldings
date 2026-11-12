module

public import Unfoldings.Geometry.SharedEdgeInterior
public import Unfoldings.Geometry.EdgePerfect
public import Unfoldings.Topology.PerfectProjection

/-! Exterior skirt cuts cannot add a whole shared edge inside the original region. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem shared_edge_subset_cutset_of_skirt (T U : Triangle) (e f : Fin 3)
    (same : T.edge e = U.edge f)
    (disjoint : Disjoint (interior T.carrier) (interior U.carrier))
    {region cuts skirt : Set Plane} (first : T.carrier ⊆ region) (last : U.carrier ⊆ region)
    (closed : IsClosed cuts) (outside : ∀ p ∈ skirt, p ∉ interior region)
    (selected : T.edge e ⊆ cuts ∪ skirt) : T.edge e ⊆ cuts := by
  let E := T.Edge e
  let good : Set E := {x | x.val ∈ cuts}
  let bad : Set E := {x | T.IsVertex x.val}
  have closed_good : IsClosed good := closed.preimage continuous_subtype_val
  have finite_bad : bad.Finite := (Set.finite_range T.vertex).of_injOn
    (f := fun x : E => x.val) (fun _ vertex => vertex) Subtype.val_injective.injOn
  have cover : Set.range (fun x : E => x) ⊆ good ∪ bad := by
    rintro x ⟨x, rfl⟩
    by_cases vertex : T.IsVertex x.val
    · exact Or.inr vertex
    · apply Or.inl
      rcases selected x.property with member | member
      · exact member
      · exact (outside x.val member
          (T.shared_edge_mem_interior_of_subsets U e f same disjoint first last x vertex)).elim
  let : PerfectSpace E := T.edgePerfectSpace e
  have all := range_subset_closed_of_perfect (fun x : E => x) continuous_id
    closed_good finite_bad cover (fun _ _ _ equal => equal)
  intro p member
  exact all ⟨⟨p, member⟩, rfl⟩

end Unfoldings.Triangle
