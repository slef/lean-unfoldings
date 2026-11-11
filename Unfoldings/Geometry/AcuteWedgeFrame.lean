module

public import Unfoldings.Cone.CornerSector
public import Unfoldings.Geometry.AngleConeBound
public import Unfoldings.Geometry.ComplexArea

/-! A closed acute planar wedge has an orthogonal frame with positive quadrant margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

structure AcuteWedgeFrame (u v : Plane) where
  place : Plane ≃ₗᵢ[ℝ] ℂ
  first_ne : u ≠ 0
  last_ne : v ≠ 0
  margin : ℝ
  positive : 0 < margin
  small : margin ≤ Real.pi / 4
  first : place u = (‖u‖ : ℂ) * polarRay margin
  last : place v = (‖v‖ : ℂ) * polarRay (Real.pi / 2 - margin)

/-- The rigid triangle-corner frame leaves half the acute slack on each quadrant side. -/
theorem exists_acuteWedgeFrame (u v : Plane) (genuine : orient 0 u v ≠ 0)
    (acute : InnerProductGeometry.angle u v < Real.pi / 2) : Nonempty (AcuteWedgeFrame u v) := by
  let T : Triangle := ⟨![0, u, v], genuine⟩
  let frame := T.cornerFrame 0
  let θ := InnerProductGeometry.angle u v
  let δ := (Real.pi / 2 - θ) / 2
  have angle_eq : T.cornerAngle 0 = θ := by
    change InnerProductGeometry.angle (u - 0) (v - 0) = θ
    simp only [sub_zero]
    rfl
  have θpositive : 0 < θ := angle_eq ▸ T.cornerAngle_pos 0
  have δpositive : 0 < δ := by dsimp [δ]; linarith
  have δsmall : δ ≤ Real.pi / 4 := by dsimp [δ]; linarith
  have une : u ≠ 0 := by intro zero; simp [zero, orient] at genuine
  have vne : v ≠ 0 := by intro zero; simp [zero, orient] at genuine
  have apex : frame.place (0 : Plane) = 0 := frame.apex
  have first_point : frame.place u = (‖u‖ : ℂ) := by
    have first := frame.first
    change frame.place u = (dist (0 : Plane) u : ℂ) at first
    simpa only [dist_zero_left] using first
  have last_point : frame.place v = (‖v‖ : ℂ) * polarRay θ := by
    have last := frame.second_polar
    change frame.place v = (dist (0 : Plane) v : ℂ) * polarRay (T.cornerAngle 0) at last
    simpa only [dist_zero_left, angle_eq] using last
  let L := frame.place.linearIsometryEquiv
  have first_vector : L u = (‖u‖ : ℂ) := by
    have linear := frame.place.map_vsub u 0
    simpa only [vsub_eq_sub, sub_zero, apex, first_point] using linear
  have last_vector : L v = (‖v‖ : ℂ) * polarRay θ := by
    have linear := frame.place.map_vsub v 0
    simpa only [vsub_eq_sub, sub_zero, apex, last_point] using linear
  let R := L.trans (_root_.rotation (Circle.exp δ))
  refine ⟨⟨R, une, vne, δ, δpositive, δsmall, ?_, ?_⟩⟩
  · change polarRay δ * L u = (‖u‖ : ℂ) * polarRay δ
    rw [first_vector]
    ring
  · change polarRay δ * L v = (‖v‖ : ℂ) * polarRay (Real.pi / 2 - δ)
    rw [last_vector]
    have sum : δ + θ = Real.pi / 2 - δ := by dsimp [δ]; ring
    rw [← sum, polarRay_add]
    ring

end Unfoldings
