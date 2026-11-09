module

public import Unfoldings.Metric.Polygonal

/-! The planar development and its inverse are locally isometric on open regions. -/

@[expose] public section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem ofSubtype_isometric_neighborhood (is_open : IsOpen s) (x : s) :
    ∃ T : Set s, IsOpen T ∧ x ∈ T ∧
      Isometry (fun y : T => ofSubtype y.val) := by
  obtain ⟨r, positive, included⟩ := Metric.isOpen_iff.mp is_open x.val x.property
  let T : Set s := Subtype.val ⁻¹' Metric.ball x.val r
  refine ⟨T, Metric.isOpen_ball.preimage continuous_subtype_val,
    Metric.mem_ball_self positive, ?_⟩
  intro a b
  exact edist_eq_of_segment
    (((convex_ball x.val r).segment_subset a.property b.property).trans included)

theorem val_isometric_neighborhood (is_open : IsOpen s) (x : PolygonalPoint s) :
    ∃ T : Set (PolygonalPoint s), IsOpen T ∧ x ∈ T ∧
      Isometry (fun y : T => y.val.val) := by
  obtain ⟨r, positive, included⟩ := Metric.isOpen_iff.mp is_open x.val x.property
  let T : Set (PolygonalPoint s) := val ⁻¹' Metric.ball x.val r
  refine ⟨T, Metric.isOpen_ball.preimage ambient_lipschitz.continuous,
    Metric.mem_ball_self positive, ?_⟩
  intro a b
  exact (edist_eq_of_segment
    (((convex_ball x.val r).segment_subset a.property b.property).trans included)).symm

end Unfoldings.PolygonalPoint
