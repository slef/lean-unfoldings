module

public import Unfoldings.Geometry.ConformingStar
public import Unfoldings.Topology.PuncturedJordanNeighborhood

/-! Point-copy compatibility in conforming triangulations of Jordan disks. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.TriangleFamily

variable {I Y : Type*} [Finite I] (triangle : I → Triangle)

/-- Agreement along whole edges forces agreement at all copies of a point in a conforming
Jordan disk. The domain need not be convex, and boundary vertices may be reflex. -/
theorem incident_values_eq_of_ambientDisk {S : Set Plane} (h : Plane ≃ₜ Plane)
    (image : h '' S = Metric.closedBall (0 : Plane) 1)
    (cover : (⋃ i, (triangle i).carrier) = S) (conforming : Conforming triangle)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)))
    (p : Plane) (value : {i // p ∈ (triangle i).carrier} → Y)
    (agree : ∀ a b, ∀ e f : Fin 3, (triangle a.val).edge e = (triangle b.val).edge f →
      p ∈ (triangle a.val).edge e → value a = value b)
    (a b : {i // p ∈ (triangle i).carrier}) : value a = value b := by
  classical
  have triangle_subset (i : I) : (triangle i).carrier ⊆ S :=
    (Set.subset_iUnion (fun j => (triangle j).carrier) i).trans cover.subset
  have exclude (i : I) : ∀ᶠ q in 𝓝 p, q ∈ (triangle i).carrier → p ∈ (triangle i).carrier := by
    by_cases member : p ∈ (triangle i).carrier
    · exact Eventually.of_forall (fun _ _ => member)
    · filter_upwards [(triangle i).compact_carrier.isClosed.isOpen_compl.mem_nhds member]
        with q outside
      exact fun inside => (outside inside).elim
  have avoid (i : I × Fin 3) : ∀ᶠ q in 𝓝 p, q = (triangle i.1).vertex i.2 → q = p := by
    by_cases equal : (triangle i.1).vertex i.2 = p
    · exact Eventually.of_forall (fun _ same => same.trans equal)
    · filter_upwards [isOpen_compl_singleton.mem_nhds (Ne.symm equal)] with q outside
      exact fun same => (outside same).elim
  have near := (Filter.eventually_all.mpr exclude).and (Filter.eventually_all.mpr avoid)
  obtain ⟨r, positive, controlled⟩ := Metric.eventually_nhds_iff.mp near
  obtain ⟨N, open_N, in_N, small_N, connected⟩ :=
    PlanarTopology.exists_punctured_connected_neighborhood h image
      (triangle_subset a.val a.property) positive
  let U := (S ∩ N) \ {p}
  let := Subtype.preconnectedSpace connected
  let Incident := {i // p ∈ (triangle i).carrier}
  let piece (i : Incident) : Set U := {q | q.val ∈ (triangle i.val).carrier}
  have closed (i : Incident) : IsClosed (piece i) :=
    (triangle i.val).compact_carrier.isClosed.preimage continuous_subtype_val
  have pieces_cover : (⋃ i, piece i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (cover.symm ▸ q.property.1.1)
    have incident := (controlled (small_N q.property.1.2)).1 i member
    exact Set.mem_iUnion.mpr ⟨⟨i, incident⟩, member⟩
  have compatible (i j : Incident) (meeting : (piece i ∩ piece j).Nonempty) :
      value i = value j := by
    by_cases same : i.val = j.val
    · exact congrArg value (Subtype.ext same)
    · obtain ⟨q, first, last⟩ := meeting
      rcases conforming i.val j.val same q.val ⟨first, last⟩ with vertices | ⟨e, f, shared, _⟩
      · obtain ⟨k, at_vertex⟩ := vertices.1
        have at_p := (controlled (small_N q.property.1.2)).2 (i.val, k) at_vertex.symm
        exact (q.property.2 at_p).elim
      · have through_p : p ∈ (triangle i.val).edge e :=
          ((triangle i.val).inter_eq_shared_edge (triangle j.val) e f shared
            (separated same)).subset ⟨i.property, j.property⟩
        exact agree i j e f shared through_p
  obtain ⟨δ, δpos, in_neighborhood⟩ := Metric.isOpen_iff.mp open_N p in_N
  have piece_nonempty (i : Incident) : (piece i).Nonempty := by
    obtain ⟨q, inside, close, different⟩ :=
      (triangle i.val).exists_near_interior_ne i.property δpos
    have member : q ∈ (triangle i.val).carrier := interior_subset inside
    exact ⟨⟨q, ⟨triangle_subset i.val member, in_neighborhood close⟩, different⟩, member⟩
  exact eq_of_finite_closed_cover piece closed pieces_cover value compatible
    (piece_nonempty a) (piece_nonempty b)

end Unfoldings.TriangleFamily
