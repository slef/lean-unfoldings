module

public import Unfoldings.Convex.FiniteDual
public import Unfoldings.Geometry.AffineEnvelopeDomainPartition

/-! Affine partitions of finite dual costs on compact slope polygons. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteDual

universe u

variable {I : Type u} [Fintype I] [Nonempty I]
  (point : I → Plane) (level : I → ℝ)

def negativePlane (i : I) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane (level i) - (innerSL ℝ (point i)).toLinearMap.toAffineMap

omit [Fintype I] [Nonempty I] in
@[simp] theorem negativePlane_apply (i : I) (p : Plane) :
    negativePlane point level i p = level i - inner ℝ (point i) p := rfl

theorem negative_cost (p : Plane) :
    AffineEnvelope.height (negativePlane point level) p = -cost point level p := by
  apply le_antisymm
  · obtain ⟨i, equal⟩ := exists_cost_eq point level p
    have bound := AffineEnvelope.height_le (negativePlane point level) p i
    rw [negativePlane_apply] at bound
    linarith
  · obtain ⟨i, equal⟩ := AffineEnvelope.exists_height_eq (negativePlane point level) p
    rw [negativePlane_apply] at equal
    have bound := vertex_le point level p i
    linarith

/-- Construct a finite triangle partition of the clipping polygon on each triangle of
which the actual finite dual cost is affine. -/
theorem exists_cost_partition {J : Type u} [Fintype J] [Nonempty J]
    (domain : J → Plane →ᵃ[ℝ] ℝ) {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    ∃ (A : Type u) (_ : Finite A) (triangle : A → Triangle) (plane : A → I),
      AffineEnvelope.clip domain Z = ⋃ a, (triangle a).carrier ∧
      (∀ a p, p ∈ (triangle a).carrier →
        cost point level p = inner ℝ (point (plane a)) p - level (plane a)) := by
  obtain ⟨A, finite, triangle, plane, cover, _separated, active⟩ :=
    AffineEnvelope.exists_domain_triangle_partition (negativePlane point level) domain compact
      higher
  refine ⟨A, finite, triangle, plane, cover, ?_⟩
  intro a p hp
  have equal := active a p hp
  rw [negative_cost, negativePlane_apply] at equal
  linarith

end Unfoldings.FiniteDual
