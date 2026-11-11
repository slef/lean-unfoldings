module

public import Unfoldings.Cap.SectionPotentialIdentity
public import Unfoldings.Cap.AnchorTrace
public import Unfoldings.Geometry.PolarAngleBound

/-!
# Uniform actual developed heading bounds from a common rim face

The entire actual signed phase sum is at most twice total curvature. Together
with the actual spatial turn bound, a regular section's real unreduced developed
heading changes by at most twice the tilt plus twice total curvature. The same
original rim face serves as anchor for every requested original face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- A whole actual regular trace has a mesh-independent real developed heading bound. -/
theorem exists_uniform_trace_heading (D : FacewiseDevelopment C M.retain)
    (positive : 0 < t) (small : t < 1) {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (tilt_small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    ∃ heading : Fin (T.turns + 1) → ℝ,
      heading 0 = (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face 0) (q - p))).arg ∧
      (∀ i, NormedSpace.normalize (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K (T.face i) (q - p))) = polarRay (heading i)) ∧
      |heading (Fin.last T.turns) - heading 0| ≤
        2 * φ + 2 * C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨phase, heading, actual, first, realizes, residual⟩ :=
    M.exists_actual_trace_heading D T different regular nonnegative tilt_small tilt
  have phase_bound :=
    M.abs_sum_actualSectionPhases_le positive small T different regular phase actual
  have residual_bounds := abs_le.mp residual
  have phase_bounds := abs_le.mp phase_bound
  exact ⟨heading, first, realizes, abs_le.mpr
    ⟨by linarith [residual_bounds.1, phase_bounds.1],
      by linarith [residual_bounds.2, phase_bounds.2]⟩⟩

/-- Every original face has a section direction uniformly close in real heading to one anchor. -/
theorem exists_face_section_heading (D : FacewiseDevelopment C M.retain)
    (positive : 0 < t) (small : t < 1) (A : K.RimAnchor) (f : Face)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (tilt_small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    ∃ q ∈ interior (K.projectedTriangle f).carrier, ∃ first last : ℝ,
      q ≠ A.point ∧
      NormedSpace.normalize (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K A.bank.val.face (q - A.point))) = polarRay first ∧
      NormedSpace.normalize (D.boundaryCycleFrame M.projectionContour.cycle
        (D.developedDirection K f (q - A.point))) = polarRay last ∧
      |last - first| ≤ 2 * φ + 2 * C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨q, inside, T, different, first_face, last_face, regular⟩ :=
    A.exists_regular_face_trace_to f
  obtain ⟨heading, _first, realizes, bound⟩ := M.exists_uniform_trace_heading D positive small T
    different.symm regular nonnegative tilt_small tilt
  have first := realizes 0
  have last := realizes (Fin.last T.turns)
  rw [first_face] at first
  rw [last_face] at last
  exact ⟨q, inside, heading 0, heading (Fin.last T.turns), different, first, last, bound⟩

/-- Every actual original face has a direction aligned uniformly with the same anchor face. -/
theorem exists_face_section_angle (D : FacewiseDevelopment C M.retain)
    (positive : 0 < t) (small : t < 1) (A : K.RimAnchor) (f : Face)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (tilt_small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    ∃ q ∈ interior (K.projectedTriangle f).carrier, q ≠ A.point ∧
      InnerProductGeometry.angle (D.developedDirection K A.bank.val.face (q - A.point))
        (D.developedDirection K f (q - A.point)) ≤
          2 * φ + 2 * C.totalInteriorAngularDefect Set.univ := by
  obtain ⟨q, inside, first, last, different, initial, final, bound⟩ :=
    M.exists_face_section_heading D positive small A f nonnegative tilt_small tilt
  let L := D.boundaryCycleFrame M.projectionContour.cycle
  refine ⟨q, inside, different, ?_⟩
  calc
    _ = InnerProductGeometry.angle
        (L (D.developedDirection K A.bank.val.face (q - A.point)))
        (L (D.developedDirection K f (q - A.point))) :=
      (L.toLinearIsometry.angle_map _ _).symm
    _ = InnerProductGeometry.angle
        (NormedSpace.normalize (L (D.developedDirection K A.bank.val.face (q - A.point))))
        (NormedSpace.normalize (L (D.developedDirection K f (q - A.point)))) := by
      rw [InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right]
    _ = InnerProductGeometry.angle (polarRay first) (polarRay last) := by rw [initial, final]
    _ ≤ |last - first| := angle_polarRay_le_abs_sub first last
    _ ≤ _ := bound

end Unfoldings.ConvexCap.SectorForest
