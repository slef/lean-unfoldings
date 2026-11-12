module

public import Unfoldings.Cap.ProjectedDevelopedMap

/-! Only finitely many sweep heights can contain actual projected mesh vertices. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def framedVertexHeights (source : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ) : Set ℝ :=
  Set.range (fun w : C.Vertex Set.univ =>
    (frame (K.projectedVertex w - source)).re + (frame (K.projectedVertex w - source)).im)

theorem finite_framedVertexHeights (source : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ) :
    (K.framedVertexHeights source frame).Finite := Set.finite_range _

/-- This test is physical and independent of any development or bank copy. -/
theorem regular_of_not_framedVertexHeights (source : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {z : ℂ} (outside : z.re + z.im ∉ K.framedVertexHeights source frame) :
    ∀ f j, source + frame.symm z ≠ (K.projectedTriangle f).vertex j := by
  intro f j equal
  let w := C.vertexOfCorner Set.univ (f, j)
  have physical : source + frame.symm z = K.projectedVertex w := equal
  have inverse : frame.symm z = K.projectedVertex w - source := by
    rw [← physical]
    abel
  have input : z = frame (K.projectedVertex w - source) := by
    simpa only [frame.apply_symm_apply] using congrArg frame inverse
  apply outside
  refine ⟨w, ?_⟩
  change (frame (K.projectedVertex w - source)).re +
    (frame (K.projectedVertex w - source)).im = z.re + z.im
  rw [← input]

end Unfoldings.ConvexCap
