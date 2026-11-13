module

public import Unfoldings.Roof.CompletionMesh
public import Unfoldings.Geometry.SpatialEnvelopeAlignment

/-! Refine an existing physical roof completion without changing its height function or domain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- Prescribed line refinement preserves the physical completion and its entire tilt budget. -/
def alignToLines {A : Type u} [Finite A] (equation : A → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ a, equation a ≠ 0) : K.CompletionMesh φ region equation where
  tentHeight := E.tentHeight
  level := E.level
  mesh := E.mesh.toTriangulation.alignToLines equation proper E.interior_nonempty
  conforming := E.mesh.toTriangulation.alignToLines_conforming equation proper E.interior_nonempty
  covers := E.covers
  unchanged := E.unchanged

/-- Every new physical triangle has an actual old parent carrying the same supporting plane. -/
theorem alignToLines_subordinate {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0) :
    let L := E.alignToLines equation proper
    ∃ parent : L.mesh.Index → E.mesh.Index, ∀ i,
      (L.mesh.projectedTriangle i).carrier ⊆ (E.mesh.projectedTriangle (parent i)).carrier ∧
        L.mesh.support i = E.mesh.support (parent i) :=
  E.mesh.toTriangulation.alignToLines_subordinate equation proper E.interior_nonempty

end Unfoldings.ConvexRoof.CompletionMesh
