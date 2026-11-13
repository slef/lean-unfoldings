module

public import Unfoldings.Roof.CompletionMesh

/-! The actual support family and convex domain of a physical roof completion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : K.CompletionMesh φ region extra)

abbrev supportPlanes : Face ⊕ (Bool × Bool) → SpatialPlane :=
  K.completionPlanes T.tentHeight (Real.sin φ / 2)

abbrev domain : Set Plane := SpatialEnvelope.clip T.supportPlanes T.level

end Unfoldings.ConvexRoof.CompletionMesh
