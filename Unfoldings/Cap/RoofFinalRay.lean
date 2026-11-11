module

public import Unfoldings.Cap.RoofCellTrace
public import Unfoldings.Geometry.FiniteAffineTail

/-! Every ray on the unbounded roof eventually stays in one actual original support cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem supportHeight_on_ray (f : Face) (p direction : Plane) (a : ℝ) :
    K.supportHeight f (p + a • direction) =
      K.supportHeight f p + a * (-inner ℝ (K.normalSlope f) direction) := by
  rw [K.supportHeight_difference f p, add_sub_cancel_left, inner_smul_right]
  ring

/-- The finite support family has one fixed active face beyond a finite ray threshold. -/
theorem exists_final_roofCell (p direction : Plane) :
    ∃ f : Face, ∃ T : ℝ, 0 < T ∧ ∀ a, T ≤ a → p + a • direction ∈ K.roofCell f := by
  let := K.nonempty_face
  obtain ⟨f, T, positive, least⟩ := exists_final_affine_minimizer
    (fun f => K.supportHeight f p) (fun f => -inner ℝ (K.normalSlope f) direction)
  refine ⟨f, T, positive, fun a after g => ?_⟩
  rw [K.supportHeight_on_ray, K.supportHeight_on_ray]
  exact least a after g

/-- Beyond that threshold, the actual spatial ray is straight with the true support-face tangent. -/
theorem exists_final_straight_roof_ray (p direction : Plane) :
    ∃ f : Face, ∃ T : ℝ, 0 < T ∧ ∀ a, T ≤ a →
      K.roofPoint (p + a • direction) =
        K.roofPoint (p + T • direction) + (a - T) • K.spatialDirection f direction := by
  obtain ⟨f, T, positive, active⟩ := K.exists_final_roofCell p direction
  refine ⟨f, T, positive, fun a after => ?_⟩
  have first := (K.mem_roofCell_iff _ _).mp (active T le_rfl)
  have last := (K.mem_roofCell_iff _ _).mp (active a after)
  have height := K.supportHeight_on_ray f p direction a
  have start := K.supportHeight_on_ray f p direction T
  rw [K.spatialDirection_eq_section]
  ext i
  fin_cases i
  · change p 0 + a * direction 0 = p 0 + T * direction 0 + (a - T) * direction 0
    ring
  · change p 1 + a * direction 1 = p 1 + T * direction 1 + (a - T) * direction 1
    ring
  · change K.roofHeight (p + a • direction) = K.roofHeight (p + T • direction) +
      (a - T) * (-inner ℝ (K.normalSlope f) direction)
    rw [first, last, height, start]
    ring

end Unfoldings.ConvexCap
