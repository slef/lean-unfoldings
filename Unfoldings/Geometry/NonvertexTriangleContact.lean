module

public import Unfoldings.Geometry.TriangleFrontier
public import Unfoldings.Geometry.TriangleNeighborhood

/-! An isolated contact of two genuine triangles contains a corner of at least one triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- A common nonvertex point of two triangles is approached by different common points. -/
theorem exists_near_common_point_of_nonvertices (T U : Triangle) {p : Plane}
    (first : p ∈ T.carrier) (last : p ∈ U.carrier)
    (regular_first : ¬ T.IsVertex p) (regular_last : ¬ U.IsVertex p)
    {V : Set Plane} (opened : IsOpen V) (member : p ∈ V) :
    ∃ q ∈ T.carrier ∩ U.carrier ∩ V, q ≠ p := by
  have interior_case (A B : Triangle) (inside : p ∈ interior A.carrier)
      (other : p ∈ B.carrier) : ∃ q ∈ A.carrier ∩ B.carrier ∩ V, q ≠ p := by
    obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp (isOpen_interior.inter opened) p
      ⟨inside, member⟩
    obtain ⟨q, q_inside, near, different⟩ := B.exists_near_interior_ne other positive
    have local_member := ball (show q ∈ Metric.ball p r from near)
    exact ⟨q, ⟨⟨interior_subset local_member.1, interior_subset q_inside⟩, local_member.2⟩,
      different⟩
  by_cases inside_first : p ∈ interior T.carrier
  · exact interior_case T U inside_first last
  by_cases inside_last : p ∈ interior U.carrier
  · obtain ⟨q, ⟨⟨in_last, in_first⟩, in_region⟩, different⟩ :=
      interior_case U T inside_last first
    exact ⟨q, ⟨⟨in_first, in_last⟩, in_region⟩, different⟩
  obtain ⟨e, on_first⟩ := T.exists_edge_of_not_mem_interior ⟨p, first⟩ inside_first
  obtain ⟨f, on_last⟩ := U.exists_edge_of_not_mem_interior ⟨p, last⟩ inside_last
  let height := U.coord (next (next f))
  have zero : height p = 0 := U.coord_edge_eq_zero f ⟨p, on_last⟩
  have endpoint : ∃ a : Plane, T.IsVertex a ∧ a ∈ T.edge e ∧ 0 ≤ height a := by
    by_cases left : 0 ≤ height (T.vertex e)
    · exact ⟨T.vertex e, ⟨e, rfl⟩, left_mem_segment ℝ _ _, left⟩
    by_cases right : 0 ≤ height (T.vertex (next e))
    · exact ⟨T.vertex (next e), ⟨next e, rfl⟩, right_mem_segment ℝ _ _, right⟩
    have negative : Convex ℝ {x : Plane | height x < 0} :=
      (convex_Iio (0 : ℝ)).affine_preimage height
    have impossible := negative.segment_subset (lt_of_not_ge left) (lt_of_not_ge right) on_first
    exact (lt_irrefl (0 : ℝ) (zero ▸ impossible)).elim
  obtain ⟨a, vertex, on_edge, nonnegative⟩ := endpoint
  have different : p ≠ a := fun same => regular_first (same.symm ▸ vertex)
  obtain ⟨r, positive, halfplane⟩ := U.exists_ball_halfplane_edge f ⟨p, on_last⟩ regular_last
  have neighborhood : IsOpen (Metric.ball p r ∩ V) := Metric.isOpen_ball.inter opened
  obtain ⟨δ, δpositive, ball⟩ := Metric.isOpen_iff.mp neighborhood p
    ⟨Metric.mem_ball_self positive, member⟩
  have approached : p ∈ closure (openSegment ℝ p a) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ p a)
  obtain ⟨q, between, near⟩ := Metric.mem_closure_iff.mp approached δ δpositive
  have local_member := ball (show q ∈ Metric.ball p δ by
    simpa only [Metric.mem_ball, dist_comm] using near)
  have segment_member := openSegment_subset_segment ℝ p a between
  have on_T := T.convex_carrier.segment_subset first (T.edge_subset e on_edge) segment_member
  have nonnegative_region : Convex ℝ {x : Plane | 0 ≤ height x} :=
    (convex_Ici (0 : ℝ)).affine_preimage height
  have on_U := (halfplane q local_member.1).mpr
    (nonnegative_region.segment_subset zero.ge nonnegative segment_member)
  refine ⟨q, ⟨⟨on_T, on_U⟩, local_member.2⟩, ?_⟩
  intro same
  exact different (left_mem_openSegment_iff.mp (same ▸ between))

/-- An isolated closed contact forces at least one actual triangle corner. -/
theorem isVertex_or_isVertex_of_isolated_contact (T U : Triangle) {p : Plane}
    (first : p ∈ T.carrier) (last : p ∈ U.carrier)
    {V : Set Plane} (opened : IsOpen V) (member : p ∈ V)
    (isolated : ∀ q ∈ T.carrier ∩ U.carrier ∩ V, q = p) :
    T.IsVertex p ∨ U.IsVertex p := by
  by_contra neither
  push Not at neither
  obtain ⟨q, contact, different⟩ := T.exists_near_common_point_of_nonvertices U first last
    neither.1 neither.2 opened member
  exact different (isolated q contact)

end Unfoldings.Triangle
