module

public import Unfoldings.Cap.CompletedParentBankSides

/-! Actual geometric signed phases for completed parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (R : K.RadialCutForest source cuts)

/-- The actual signed parent-bank rotation selected by the geometric transverse crossing. -/
def parentSectionPhase (e : C.Vertex Set.univ) (direction : Plane) : ℝ :=
  if 0 < orient 0 (K.projectedVertex (R.spanningCompletion.parents.parent e) - K.projectedVertex
    e) direction then
    R.completedSubtreeCurvature e else -R.completedSubtreeCurvature e

namespace ParentBankOpening

variable {R} {D : FacewiseDevelopment C R.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}} (B : R.ParentBankOpening
    D e)

/-- The constructed actual banks name exactly the two incident original faces. -/
theorem face_order_iff (f g : Face) :
    ((f = (C.left (R.spanningCompletion.selection.edge e)).face ∧ g = (C.right
      (R.spanningCompletion.selection.edge e)).face) ∨
      (f = (C.right (R.spanningCompletion.selection.edge e)).face ∧ g = (C.left
        (R.spanningCompletion.selection.edge e)).face)) ↔
    ((f = B.entranceFace ∧ g = B.exitFace) ∨ (f = B.exitFace ∧ g = B.entranceFace)) := by
  rw [B.entranceFace_eq, B.exitFace_eq]
  cases B.side
  · rfl
  · exact or_comm

/-- The actual geometric crossing phase removes all but the genuine spatial section bend. -/
theorem crossing_turn_le {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns)
    (faces : (T.face i.castSucc = B.entranceFace ∧ T.face i.succ = B.exitFace) ∨
      (T.face i.castSucc = B.exitFace ∧ T.face i.succ = B.entranceFace))
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (R.spanningCompletion.selection.edge e)).face).edge
        (C.left (R.spanningCompletion.selection.edge e)).edge) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame R.completedContour.cycle
        (D.developedDirection K (T.face i.castSucc) (q - p)))
      (polarRay (-R.parentSectionPhase e.val (q - p)) *
        D.boundaryCycleFrame R.completedContour.cycle
          (D.developedDirection K (T.face i.succ) (q - p))) ≤
      InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
        (K.spatialDirection (T.face i.succ) (q - p)) := by
  rcases faces with forward | backward
  · have sign := B.entrance_crossing_sign T different regular i forward.1 crossing
    simp only [parentSectionPhase, ite_eq_left sign]
    rw [forward.1, forward.2]
    exact B.section_turn_le (q - p) sign.ne'
  · have sign := B.exit_crossing_sign T different regular i backward.1 crossing
    simp only [parentSectionPhase, ite_eq_right (not_lt_of_ge sign.le), neg_neg]
    rw [backward.1, backward.2]
    exact B.reverse_section_turn_le (q - p) sign.ne

end ParentBankOpening
end Unfoldings.ConvexCap.RadialCutForest
