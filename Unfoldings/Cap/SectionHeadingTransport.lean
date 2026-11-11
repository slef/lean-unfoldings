module

public import Unfoldings.Cap.SectionTraceTurns
public import Unfoldings.Geometry.ComplexHeadingTransport

/-!
# Real heading transport along actual cap section traces

Once actual seam phases are identified, spatial section turning contributes at
most twice the tilt to the real developed heading error. Signed phases remain
inside a single sum; their crossing-budget estimate is a separate hypothesis
of this transport lemma.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectionFaceTrace

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (L : Plane ≃ₗᵢ[ℝ] ℂ)

/-- Actual section traces convert local phase-corrected bounds into a uniform real heading bound. -/
theorem exists_heading_transport (different : p ≠ q)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (phase : Fin T.turns → ℝ)
    (local_bound : ∀ i, InnerProductGeometry.angle
      (L (D.developedDirection K (T.face i.castSucc) (q - p)))
      (polarRay (-phase i) * L (D.developedDirection K (T.face i.succ) (q - p))) ≤
      InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
        (K.spatialDirection (T.face i.succ) (q - p))) :
    ∃ heading : Fin (T.turns + 1) → ℝ,
      heading 0 = (L (D.developedDirection K (T.face 0) (q - p))).arg ∧
      (∀ i, NormedSpace.normalize (L (D.developedDirection K (T.face i) (q - p))) =
        polarRay (heading i)) ∧
      |heading (Fin.last T.turns) - heading 0 - ∑ i, phase i| ≤ 2 * φ := by
  have genuine (i : Fin (T.turns + 1)) :
      L (D.developedDirection K (T.face i) (q - p)) ≠ 0 := by
    simpa only [map_zero] using L.injective.ne
      (D.developedDirection_ne_zero K (T.face i) (sub_ne_zero.mpr different.symm))
  obtain ⟨heading, first, realizes, bound⟩ := exists_complex_heading_transport
    (fun i => L (D.developedDirection K (T.face i) (q - p))) genuine phase
    (fun i => InnerProductGeometry.angle (K.spatialDirection (T.face i.castSucc) (q - p))
      (K.spatialDirection (T.face i.succ) (q - p))) local_bound
  exact ⟨heading, first, realizes,
    bound.trans (T.sum_spatialDirection_turn_le_tilt different nonnegative small tilt)⟩

end Unfoldings.ConvexCap.SectionFaceTrace
