module

public import Unfoldings.Geometry.HalfOpenStraightGraph
public import Unfoldings.Geometry.CommonInitialSubsegments

/-! Oriented subdivision preserves uniqueness of the forward edge of a straight embedded graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (G : FiniteEmbeddedGraph V E X)

/-- A genuine forward portion of one actual coarse edge, with both affine parameters retained. -/
structure OrientedSubsegment (a b : X) where
  edge : E
  first : ℝ
  last : ℝ
  first_mem : first ∈ Set.Icc 0 1
  last_mem : last ∈ Set.Icc 0 1
  increasing : first < last
  at_first : AffineMap.lineMap (G.vertex (G.left edge)) (G.vertex (G.right edge)) first = a
  at_last : AffineMap.lineMap (G.vertex (G.left edge)) (G.vertex (G.right edge)) last = b

namespace OrientedSubsegment

variable {G} {a b c : X} (P : G.OrientedSubsegment a b)

theorem first_mem_halfOpen (straight : G.IsStraight) :
    a ∈ Set.diff (segment ℝ (G.vertex (G.left P.edge)) (G.vertex (G.right P.edge)))
      {G.vertex (G.right P.edge)} := by
  have member : a ∈ segment ℝ (G.vertex (G.left P.edge)) (G.vertex (G.right P.edge)) := by
    exact (congrArg (fun z : X => z ∈ segment ℝ (G.vertex (G.left P.edge))
      (G.vertex (G.right P.edge))) P.at_first).mp
        (lineMap_mem_segment ℝ _ _ P.first_mem)
  refine ⟨member, ?_⟩
  intro equal
  change a = G.vertex (G.right P.edge) at equal
  have at_one : AffineMap.lineMap (G.vertex (G.left P.edge)) (G.vertex (G.right P.edge)) P.first =
      AffineMap.lineMap (G.vertex (G.left P.edge)) (G.vertex (G.right P.edge)) (1 : ℝ) :=
    P.at_first.trans (equal.trans (AffineMap.lineMap_apply_one _ _).symm)
  have one := AffineMap.lineMap_injective ℝ
    (G.vertex_injective.ne (straight.endpoints_ne P.edge)) at_one
  linarith [P.increasing, P.last_mem.2]

theorem edge_eq (straight : G.IsStraight) (outgoing : Function.Injective G.left)
    (Q : G.OrientedSubsegment a c) : P.edge = Q.edge := by
  by_contra different
  exact Set.disjoint_left.mp (straight.halfOpen_segments_disjoint outgoing different)
    (P.first_mem_halfOpen straight) (Q.first_mem_halfOpen straight)

include P in
theorem open_inter_nonempty (straight : G.IsStraight) (outgoing : Function.Injective G.left)
    (Q : G.OrientedSubsegment a c) : (openSegment ℝ a b ∩ openSegment ℝ a c).Nonempty := by
  have same_edge := P.edge_eq straight outgoing Q
  have first_point : AffineMap.lineMap (G.vertex (G.left P.edge))
      (G.vertex (G.right P.edge)) Q.first = a := by
    rw [same_edge]
    exact Q.at_first
  have same_first := AffineMap.lineMap_injective ℝ
    (G.vertex_injective.ne (straight.endpoints_ne P.edge)) (P.at_first.trans first_point.symm)
  have last_point : AffineMap.lineMap (G.vertex (G.left P.edge))
      (G.vertex (G.right P.edge)) Q.last = c := by
    rw [same_edge]
    exact Q.at_last
  have ordered : P.first < Q.last := by
    rw [same_first]
    exact Q.increasing
  have meeting := openSubsegments_inter_nonempty (G.vertex (G.left P.edge))
    (G.vertex (G.right P.edge)) P.increasing ordered
  rw [P.at_first, P.at_last, last_point] at meeting
  exact meeting

end OrientedSubsegment

variable {W F : Type*} {H : FiniteEmbeddedGraph W F X}

/-- Two forward fine edges at the same vertex must be the same edge. -/
theorem fine_forward_edge_unique (straight : G.IsStraight) (outgoing : Function.Injective G.left)
    (fine_straight : H.IsStraight) {e f : F} {u v w : W}
    (first : H.graph.IsLink e u v) (last : H.graph.IsLink f u w)
    (P : G.OrientedSubsegment (H.vertex u) (H.vertex v))
    (Q : G.OrientedSubsegment (H.vertex u) (H.vertex w)) : e = f := by
  by_contra different
  obtain ⟨x, hx, hy⟩ := P.open_inter_nonempty straight outgoing Q
  exact Set.disjoint_left.mp (fine_straight.openSegments_disjoint different first last) hx hy

end Unfoldings.FiniteEmbeddedGraph
