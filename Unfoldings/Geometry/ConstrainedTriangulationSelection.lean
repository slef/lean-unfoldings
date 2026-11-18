module

public import Unfoldings.Geometry.SpatialEnvelopeTriangles

/-! Selecting prescribed lines preserves the same physical constrained triangulation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.ConstrainedTriangulation

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ} (T : ConstrainedTriangulation family extra Z)

/-- Forget unneeded line certificates without changing triangles or support labels. -/
def selectConstraints {A : Type u} (equation : A → Plane →ᵃ[ℝ] ℝ) (choose : A → J)
    (equal : ∀ a, extra (choose a) = equation a) :
    ConstrainedTriangulation family equation Z where
  toTriangulation := T.toTriangulation
  signs i a := T.signs i (choose a)
  constrained i p member a := by
    rw [← equal a]
    exact T.constrained i p member (choose a)

@[simp] theorem selectConstraints_toTriangulation {A : Type u}
    (equation : A → Plane →ᵃ[ℝ] ℝ) (choose : A → J)
    (equal : ∀ a, extra (choose a) = equation a) :
    (T.selectConstraints equation choose equal).toTriangulation = T.toTriangulation := rfl

end Unfoldings.SpatialEnvelope.ConstrainedTriangulation
