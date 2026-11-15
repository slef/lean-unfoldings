module

public import Unfoldings.Roof.CompatibleClosedPieces

/-! Every positive compatible terminal point has exactly one full cut-line germ. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)

include no_boundary in
/-- The actual embedded forest supplies a whole neighborhood with exactly the terminal line.
This excludes all other closed parent pieces and full rays, with no isolation certificate. -/
theorem exists_terminal_cut_line_germ (r : {v // v ∈ R.parents.roots}) {t : ℝ}
    (positive : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, dist z (R.exterior.ray (R.terminalIndex r) t) < δ →
      (z ∈ R.carrier ↔ orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val) z = 0) := by
  classical
  let x := R.exterior.ray (R.terminalIndex r) t
  have open_x : x ∈ R.openPiece r.val := R.terminal_ray_mem_openPiece r positive
  have avoids (v : C.Vertex Set.univ) (different : v ≠ r.val) : x ∉ R.closedPiece v := by
    intro member
    rcases R.closedPiece_mem_open_or_vertex v member with on_open | ⟨w, at_vertex⟩
    · exact Set.disjoint_left.mp
        (K.compatible_openPieces_pairwise_disjoint compact nonempty R no_boundary different.symm)
        open_x on_open
    · apply K.compatible_openPiece_avoids_vertices compact nonempty R no_boundary r.val w
      rwa [← at_vertex]
  let others := ⋃ v : {v : C.Vertex Set.univ // v ≠ r.val}, R.closedPiece v.val
  have closed_others : IsClosed others :=
    isClosed_iUnion_of_finite (fun v => R.isClosed_closedPiece v.val)
  have outside : x ∈ othersᶜ := by
    intro member
    obtain ⟨v, inside⟩ := Set.mem_iUnion.mp member
    exact avoids v.val v.property inside
  obtain ⟨δ, δpos, isolated⟩ := Metric.isOpen_iff.mp closed_others.isOpen_compl x outside
  have forward : x ∈ rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val) := by
    dsimp only [x]
    rw [← R.terminal_lineMap r t]
    exact lineMap_mem_rayForwardHalfspace (R.terminal_endpoints_ne r) positive
  obtain ⟨ε, εpos, forward_ball⟩ := Metric.isOpen_iff.mp
    (isOpen_rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val)) x forward
  refine ⟨min δ ε, lt_min δpos εpos, ?_⟩
  intro z close
  have no_other : z ∉ others := isolated
    (Metric.mem_ball.mpr (close.trans_le (min_le_left δ ε)))
  have forward_z := forward_ball (Metric.mem_ball.mpr (close.trans_le (min_le_right δ ε)))
  constructor
  · intro member
    rw [R.carrier_eq_iUnion_closedPiece] at member
    obtain ⟨v, on_piece⟩ := Set.mem_iUnion.mp member
    have same : v = r.val := by
      by_contra different
      exact no_other (Set.mem_iUnion.mpr ⟨⟨v, different⟩, on_piece⟩)
    subst v
    rw [R.closedPiece_root r] at on_piece
    exact MetricGluing.rayCut_on_line _ _ z on_piece
  · intro zero
    obtain ⟨s, spos, expression⟩ := exists_positive_ray_parameter
      (R.terminal_endpoints_ne r) forward_z zero
    rw [R.carrier_eq_iUnion_closedPiece]
    apply Set.mem_iUnion.mpr
    refine ⟨r.val, ?_⟩
    rw [R.closedPiece_root r]
    exact ⟨⟨s, spos.le⟩, expression.symm⟩

end Unfoldings.ConvexRoof
