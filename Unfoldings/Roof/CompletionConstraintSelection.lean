module

public import Unfoldings.Roof.CompletionMesh

/-! Retain named subsets of actual completion constraints without changing the physical mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- Selecting already prescribed equations keeps the same physical triangles and support labels. -/
def selectConstraints {A : Type u} (equation : A → Plane →ᵃ[ℝ] ℝ) (choose : A → J)
    (equal : ∀ a, extra (choose a) = equation a) : K.CompletionMesh φ region equation where
  tentHeight := E.tentHeight
  level := E.level
  mesh := {
    toTriangulation := E.mesh.toTriangulation
    signs i a := E.mesh.signs i (choose a)
    constrained i x member a := by
      rw [← equal a]
      exact E.mesh.constrained i x member (choose a) }
  conforming := E.conforming
  covers := E.covers
  unchanged := E.unchanged

local instance selectedConstraintIndexFintype : Fintype E.mesh.Index :=
  @Fintype.ofFinite _ E.mesh.finite

/-- Constraint selection changes no geometric or intrinsic cap data. -/
theorem selectConstraints_cap {A : Type u} (equation : A → Plane →ᵃ[ℝ] ℝ) (choose : A → J)
    (equal : ∀ a, extra (choose a) = equation a) :
    (E.selectConstraints equation choose equal).cap = E.cap := rfl

end Unfoldings.ConvexRoof.CompletionMesh
