module

public import Unfoldings.Cap.SectionPhases
public import Unfoldings.Cap.SectionHeadingTransport

/-!
# Constructed actual signed-phase heading transport on regular cap sections

Every original-face transition supplies its actual original-seam phase. Real
unreduced developed headings are then constructed, with total residual error at
most twice the tilt. Bounding the remaining signed phase sum by the actual
forest-crossing potential is a separate geometric step.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Provenance of a phase: repeated labels or one actual transversely crossed original seam. -/
inductive ActualSectionPhase {p q : Plane} (T : K.SectionFaceTrace p q) (i : Fin T.turns) : ℝ → Prop
  | same (equal : T.face i.castSucc = T.face i.succ) : ActualSectionPhase T i 0
  | seam (s : C.Seam)
      (faces : (T.face i.castSucc = (C.left s).face ∧ T.face i.succ = (C.right s).face) ∨
        (T.face i.castSucc = (C.right s).face ∧ T.face i.succ = (C.left s).face))
      (crossing : T.point i.castSucc.succ ∈
        (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
      (transverse : orient 0 (K.projectedSeamVector s) (q - p) ≠ 0) :
      ActualSectionPhase T i (M.seamSectionPhase s (q - p))

/-- Construct the actual local phase and prove its residual turn bound. -/
theorem exists_actual_section_phase (D : FacewiseDevelopment C M.retain)
    {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) :
    ∃ phase : ℝ, M.ActualSectionPhase T i phase ∧
      InnerProductGeometry.angle
        (D.boundaryCycleFrame M.projectionContour.cycle
          (D.developedDirection K (T.face i.castSucc) (q - p)))
        (polarRay (-phase) * D.boundaryCycleFrame M.projectionContour.cycle
          (D.developedDirection K (T.face i.succ) (q - p))) ≤
        InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
          (K.spatialDirection (T.face i.succ) (q - p)) := by
  by_cases same : T.face i.castSucc = T.face i.succ
  · refine ⟨0, ActualSectionPhase.same same, ?_⟩
    simp only [neg_zero, polarRay_zero, one_mul, same]
    have spatial := K.spatialDirection_ne_zero (T.face i.succ) (sub_ne_zero.mpr different.symm)
    have developed :=
      D.developedDirection_ne_zero K (T.face i.succ) (sub_ne_zero.mpr different.symm)
    have framed : D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face i.succ) (q - p)) ≠ 0 := by
      simpa only [map_zero] using
        (D.boundaryCycleFrame M.projectionContour.cycle).injective.ne developed
    rw [InnerProductGeometry.angle_self framed, InnerProductGeometry.angle_self spatial]
  · obtain ⟨s, order, crossing, transverse⟩ :=
      T.exists_transverse_adjacent_seam different regular i same
    have faces : (T.face i.castSucc = (C.left s).face ∧ T.face i.succ = (C.right s).face) ∨
        (T.face i.castSucc = (C.right s).face ∧ T.face i.succ = (C.left s).face) :=
      order.elim (fun h => Or.inl ⟨h.1.symm, h.2.symm⟩)
        (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩)
    exact ⟨M.seamSectionPhase s (q - p), ActualSectionPhase.seam s faces crossing transverse,
      M.seam_section_turn_le D T different regular i s faces crossing transverse⟩

/-- The only remaining real heading error is the signed sum of constructed actual seam phases. -/
theorem exists_actual_trace_heading (D : FacewiseDevelopment C M.retain)
    {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    ∃ phase : Fin T.turns → ℝ, ∃ heading : Fin (T.turns + 1) → ℝ,
      (∀ i, M.ActualSectionPhase T i (phase i)) ∧
      heading 0 = (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face 0) (q - p))).arg ∧
      (∀ i, NormedSpace.normalize (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face i) (q - p))) = polarRay (heading i)) ∧
      |heading (Fin.last T.turns) - heading 0 - ∑ i, phase i| ≤ 2 * φ := by
  choose phase actual local_bound using M.exists_actual_section_phase D T different regular
  obtain ⟨heading, first, realizes, bound⟩ := T.exists_heading_transport D
    (D.boundaryCycleFrame M.projectionContour.cycle) different nonnegative small tilt
    phase local_bound
  exact ⟨phase, heading, actual, first, realizes, bound⟩

end Unfoldings.ConvexCap.SectorForest
