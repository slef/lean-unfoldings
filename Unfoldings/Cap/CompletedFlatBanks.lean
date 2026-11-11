module

public import Unfoldings.Cap.CompletedBankPositionOrder

/-! Flat completed subtrees have coincident banks, including their endpoint positions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completedSubtreeCurvature_mono {v e : C.Vertex Set.univ}
    (reaches : R.spanningCompletion.parents.Ancestor v e) :
    R.completedSubtreeCurvature v ≤ R.completedSubtreeCurvature e := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w member
    exact (R.spanningCompletion.parents.mem_descendants w e).mpr
      (((R.spanningCompletion.parents.mem_descendants w v).mp member).trans
        R.spanningCompletion.parents reaches)
  · exact fun w _ _ => K.interiorCurvature_nonneg w

theorem completedSubtreeCurvature_descendant_zero {v e : C.Vertex Set.univ}
    (reaches : R.spanningCompletion.parents.Ancestor v e)
    (flat : R.completedSubtreeCurvature e = 0) : R.completedSubtreeCurvature v = 0 :=
  le_antisymm ((R.completedSubtreeCurvature_mono reaches).trans_eq flat)
    (R.completedSubtreeCurvature_nonneg v)

/-- The aggregate positional gap also vanishes; parallel vectors alone would not suffice. -/
theorem completed_parent_position_gap_zero_of_flat
    (D : FacewiseDevelopment C R.completedRetain)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (flat : R.completedSubtreeCurvature e.val = 0) : R.parentPositionGap D e = 0 := by
  classical
  rw [R.parent_position_gap_eq_descendant_sum D e]
  apply Finset.sum_eq_zero
  intro v _
  split_ifs with reaches
  · rw [R.completed_parent_vectors_eq_of_flat v
      (R.completedSubtreeCurvature_descendant_zero reaches flat), sub_self]
  · rfl

/-- Zero-curvature branches are redundant slits, with identical banks at every parameter. -/
theorem completed_parent_points_eq_of_flat (D : FacewiseDevelopment C R.completedRetain)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (flat : R.completedSubtreeCurvature e.val = 0) (s : ℝ) :
    R.parentExitPoint D e s = R.parentEntrancePoint D e s := by
  have positions := R.completed_parent_position_gap_zero_of_flat D e flat
  have same := sub_eq_zero.mp positions
  change _ - _ = _ - _
  rw [R.completed_parent_vectors_eq_of_flat e flat]
  exact congrArg (fun p => p - s • R.parentEntryVector D e) same

/-- A coincident flat slit still has an injective physical parametrization. -/
theorem completed_flat_bank_intersection_parameter_eq
    (D : FacewiseDevelopment C R.completedRetain)
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots})
    (flat : R.completedSubtreeCurvature e.val = 0) {s r : ℝ}
    (same : R.parentEntrancePoint D e s = R.parentExitPoint D e r) : s = r := by
  rw [R.completed_parent_points_eq_of_flat D e flat r] at same
  have equal : s • R.parentEntryVector D e = r • R.parentEntryVector D e :=
    sub_right_inj.mp same
  have zero : (s - r) • R.parentEntryVector D e = 0 := by
    rw [sub_smul, equal, sub_self]
  rcases smul_eq_zero.mp zero with parameters | vector
  · exact sub_eq_zero.mp parameters
  · exact (D.developedDirection_ne_zero K (R.parentBankOpening D e).entranceFace
      (R.completed_parent_direction_ne_zero e.val e.property) vector).elim

end Unfoldings.ConvexCap.RadialCutForest
