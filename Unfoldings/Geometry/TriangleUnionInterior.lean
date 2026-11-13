module

public import Unfoldings.Geometry.ConformingTriangles

/-! Whole-edge connected triangular patches have connected interior. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleFamily

variable {I : Type*} (triangle : I → Triangle)

/-- Two different triangles are adjacent when they share a whole edge. -/
def EdgeAdjacent (i j : I) : Prop :=
  i ≠ j ∧ ∃ e f : Fin 3, (triangle i).edge e = (triangle j).edge f

/-- A finite triangular patch is the closure of its interior, including all boundary vertices. -/
theorem closure_interior_union [Finite I] :
    closure (interior (⋃ i, (triangle i).carrier)) = ⋃ i, (triangle i).carrier := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset
      (isCompact_iUnion fun i => (triangle i).compact_carrier).isClosed
  · intro p member
    obtain ⟨i, inside⟩ := Set.mem_iUnion.mp member
    have regular := (triangle i).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (triangle i).interior_nonempty
    rw [(triangle i).compact_carrier.isClosed.closure_eq] at regular
    apply closure_mono (interior_mono (Set.subset_iUnion (fun i => (triangle i).carrier) i))
    exact regular.symm ▸ inside

/-- Sharing a whole edge places a common point in the interior of the triangular union. -/
theorem exists_shared_interior_of_edgeAdjacent
    (separated : Pairwise (fun i j =>
      Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)))
    {i j : I} (adjacent : EdgeAdjacent triangle i j) :
    (interior (⋃ k, (triangle k).carrier) ∩
      (triangle i).carrier ∩ (triangle j).carrier).Nonempty := by
  obtain ⟨different, e, f, same⟩ := adjacent
  let T := triangle i
  let U := triangle j
  let H : HingePlacement T U e f (T.sharedEdgeIdentification U e f same) :=
    { place := AffineIsometryEquiv.refl ℝ Plane
      joined := fun _ => rfl
      opposite := T.opposite_of_shared_edge U e f same (separated different) }
  obtain ⟨x, regular⟩ := T.exists_edge_nonvertex e
  obtain ⟨r, positive, cover⟩ := H.exists_ball_cover x regular
  have near : Metric.ball x.val r ⊆ ⋃ k, (triangle k).carrier := by
    intro p hp
    have member : p ∈ T.carrier ∪ U.carrier := by
      simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using cover hp
    rcases member with first | last
    · exact Set.mem_iUnion.mpr ⟨i, first⟩
    · exact Set.mem_iUnion.mpr ⟨j, last⟩
  refine ⟨x.val, ⟨mem_interior_iff_mem_nhds.mpr ?_, T.edge_subset e x.property⟩, ?_⟩
  · exact Metric.mem_nhds_iff.mpr ⟨r, positive, near⟩
  · exact U.edge_subset f (same ▸ x.property)

/-- A nonempty triangular patch connected by whole-edge adjacencies has connected interior.
The conclusion allows arbitrary vertex contacts elsewhere in the patch. -/
theorem isConnected_interior_union [Nonempty I]
    (separated : Pairwise (fun i j =>
      Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)))
    (connected : ∀ i j, Relation.ReflTransGen (EdgeAdjacent triangle) i j) :
    IsConnected (interior (⋃ i, (triangle i).carrier)) := by
  let S := interior (⋃ i, (triangle i).carrier)
  let patch := fun i => S ∩ (triangle i).carrier
  have patches : ∀ i, IsConnected (patch i) := by
    intro i
    have inclusion : interior (triangle i).carrier ⊆ patch i :=
      fun p hp => ⟨interior_mono (Set.subset_iUnion (fun i => (triangle i).carrier) i) hp,
        interior_subset hp⟩
    apply ((triangle i).convex_carrier.interior.isConnected
      (triangle i).interior_nonempty).subset_closure inclusion
    have regular := (triangle i).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (triangle i).interior_nonempty
    rw [(triangle i).compact_carrier.isClosed.closure_eq] at regular
    exact fun _ member => regular.symm ▸ member.2
  have overlaps : ∀ i j, Relation.ReflTransGen (fun i j => (patch i ∩ patch j).Nonempty) i j := by
    intro i j
    refine Relation.ReflTransGen.mono ?_ i j (connected i j)
    intro a b adjacent
    obtain ⟨p, ⟨inside, first⟩, last⟩ :=
      exists_shared_interior_of_edgeAdjacent triangle separated adjacent
    exact ⟨p, ⟨inside, first⟩, inside, last⟩
  have union : (⋃ i, patch i) = S := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, patch]
    constructor
    · rintro ⟨_, inside, _⟩
      exact inside
    · intro inside
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp (interior_subset inside)
      exact ⟨i, inside, member⟩
  change IsConnected S
  rw [← union]
  exact IsConnected.iUnion_of_reflTransGen patches overlaps

end Unfoldings.TriangleFamily
