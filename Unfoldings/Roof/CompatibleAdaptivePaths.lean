module

public import Unfoldings.Roof.CompatibleAdaptiveRouting

/-! Actual attached parent links and directed histories obey the adaptive progress invariant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatibleAdaptiveRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {L : Set Plane} {r margin η : ℝ} (R : K.CompatibleAdaptiveRouting U G boundary L r margin η)

/-- The oriented links of the attached parent forest are actual original
links or original exterior rays truncated at first contact. -/
theorem parent_followsStep {v : C.Vertex Set.univ} (nonterminal : v ∉ R.parents.roots) :
    R.FollowsStep (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) := by
  by_cases root : v ∈ R.original.parents.roots
  · let x : {w // w ∈ R.original.parents.roots} := ⟨v, root⟩
    have not_terminal : x ∉ R.exterior.parents.roots := fun h => nonterminal ⟨root, h⟩
    have parent_eq : R.parents.parent v = (R.exterior.parents.parent x).val :=
      R.original.parents.attach_parent_root R.exterior.parents R.shared_height x
    obtain ⟨time, positive, contact⟩ := (R.exterior.next_spec not_terminal).1
    refine Or.inr ⟨x, 0, time, le_rfl, positive.le, ?_, ?_⟩
    · simp only [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points, x]
    · rw [parent_eq, ← R.exterior_points]
      exact contact
  · have parent_eq : R.parents.parent v = R.original.parents.parent v :=
      R.original.parents.attach_parent_nonroot R.exterior.parents R.shared_height root
    refine Or.inl ⟨⟨v, root⟩, 0, 1, le_rfl, zero_le_one, le_rfl, ?_, ?_⟩
    · simp only [zero_smul, add_zero]
    · rw [parent_eq, one_smul]
      abel

theorem parent_progress (v : C.Vertex Set.univ) :
    (G.boundaryEnvelope boundary).HistoryProgress L (K.projectedVertex v)
      (K.projectedVertex (R.parents.parent v)) := by
  by_cases terminal : v ∈ R.parents.roots
  · rw [R.parents.fixed_root v terminal]
    exact SlopeEnvelope.HistoryProgress.refl (G.boundaryEnvelope boundary) _
  · exact R.followsStep_progress (R.parent_followsStep terminal)

/-- Directed histories through both kinds of parent link preserve progress,
including when an exterior link meets a different exterior root. -/
theorem ancestor_progress {v w : C.Vertex Set.univ} (ancestor : R.parents.Ancestor v w) :
    (G.boundaryEnvelope boundary).HistoryProgress L (K.projectedVertex v) (K.projectedVertex w) := by
  obtain ⟨n, rfl⟩ := ancestor
  induction n with
  | zero => exact SlopeEnvelope.HistoryProgress.refl (G.boundaryEnvelope boundary) _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact SlopeEnvelope.HistoryProgress.trans (G.boundaryEnvelope boundary) ih (R.parent_progress _)

end Unfoldings.ConvexRoof.CompatibleAdaptiveRouting
