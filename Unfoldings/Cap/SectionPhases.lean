module

public import Unfoldings.Cap.ParentSectionPhase
public import Unfoldings.Cap.SectionSeams
public import Unfoldings.Cap.RetainedSectionTurn

/-!
# Actual local phases along regular original-face section traces

Retained seams contribute zero phase. Each actual cut seam has its unique
selected original parent; its phase is the signed descendant curvature selected
by the real transverse crossing. The local residual turn is derived for each
actual transition, without any phase or opening certificate as input.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The unique actual original parent whose selected edge is this removed seam. -/
def cutParent (s : C.Seam) (cut : s ∉ M.retain) :
    {v : C.Vertex Set.univ // v ∉ M.parents.roots} :=
  (C.selectedCutSeamEquiv M.selection).symm ⟨s, Set.mem_univ _, cut⟩

theorem cutParent_edge (s : C.Seam) (cut : s ∉ M.retain) :
    M.selection.edge (M.cutParent s cut) = s := by
  exact congrArg Subtype.val
    ((C.selectedCutSeamEquiv M.selection).apply_symm_apply ⟨s, Set.mem_univ _, cut⟩)

open scoped Classical in
/-- The actual original-seam phase; retained seams carry no curvature jump. -/
def seamSectionPhase (s : C.Seam) (direction : Plane) : ℝ :=
  if kept : s ∈ M.retain then 0 else M.parentSectionPhase (M.cutParent s kept).val direction

/-- The actual geometric phase contracts the residual turn across any actual transverse seam. -/
theorem seam_section_turn_le (D : FacewiseDevelopment C M.retain)
    {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (s : C.Seam)
    (faces : (T.face i.castSucc = (C.left s).face ∧ T.face i.succ = (C.right s).face) ∨
      (T.face i.castSucc = (C.right s).face ∧ T.face i.succ = (C.left s).face))
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (transverse : orient 0 (K.projectedSeamVector s) (q - p) ≠ 0) :
    InnerProductGeometry.angle
      (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face i.castSucc) (q - p)))
      (polarRay (-M.seamSectionPhase s (q - p)) *
        D.boundaryCycleFrame M.projectionContour.cycle
          (D.developedDirection K (T.face i.succ) (q - p))) ≤
      InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
        (K.spatialDirection (T.face i.succ) (q - p)) := by
  by_cases kept : s ∈ M.retain
  · simp only [seamSectionPhase, dite_eq_left kept, neg_zero, polarRay_zero, one_mul]
    let L := D.boundaryCycleFrame M.projectionContour.cycle
    have bound := D.retained_section_angle_le K s kept (q - p) transverse
    rcases faces with forward | backward
    · rw [forward.1, forward.2]
      exact (L.toLinearIsometry.angle_map _ _).le.trans bound
    · rw [backward.1, backward.2,
        InnerProductGeometry.angle_comm (K.spatialDirection (C.right s).face (q - p))
          (K.spatialDirection (C.left s).face (q - p))]
      have frame := L.toLinearIsometry.angle_map
        (D.developedDirection K (C.right s).face (q - p))
        (D.developedDirection K (C.left s).face (q - p))
      rw [InnerProductGeometry.angle_comm
        (D.developedDirection K (C.right s).face (q - p))
        (D.developedDirection K (C.left s).face (q - p))] at frame
      exact frame.le.trans bound
  · let e := M.cutParent s kept
    let B := M.parentBankOpening D e
    have named : M.selection.edge e = s := M.cutParent_edge s kept
    have bank_faces : (T.face i.castSucc = B.entranceFace ∧ T.face i.succ = B.exitFace) ∨
        (T.face i.castSucc = B.exitFace ∧ T.face i.succ = B.entranceFace) := by
      apply (B.face_order_iff _ _).mp
      simpa only [named] using faces
    have bank_crossing : T.point i.castSucc.succ ∈
        (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
          (C.left (M.selection.edge e)).edge := by simpa only [named] using crossing
    simpa only [seamSectionPhase, dite_eq_right kept] using
      B.crossing_turn_le T different regular i bank_faces bank_crossing

end Unfoldings.ConvexCap.SectorForest
