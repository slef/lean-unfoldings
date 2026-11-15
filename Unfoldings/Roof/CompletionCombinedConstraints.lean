module

public import Unfoldings.Roof.CompletionConstraintSelection
public import Unfoldings.Roof.CompletionOriginalConforming
public import Unfoldings.Roof.CompletionRegion

/-! One physical completion simultaneously respects new cuts and preserves the original metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {J : Type u} (extra : J → Plane →ᵃ[ℝ] ℝ)

/-- Keep every original triangle side and every new prescribed equation in the same mesh. -/
def combinedCompletionEquations : (Face × Fin 3) ⊕ J → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim K.originalEdgeEquations extra

theorem combinedCompletionEquations_ne_zero (proper : ∀ j, extra j ≠ 0)
    (i : (Face × Fin 3) ⊕ J) : K.combinedCompletionEquations extra i ≠ 0 := by
  cases i with
  | inl j => exact K.originalEdgeEquations_ne_zero j
  | inr j => exact proper j

/-- Original-side and cut constraints can be imposed while preserving all requested heights. -/
theorem exists_combined_completion {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2)
    {region : Set Plane} (compact : IsCompact region) [Finite J] (proper : ∀ j, extra j ≠ 0) :
    ∃ E : K.CompletionMesh φ region (K.combinedCompletionEquations extra), ∀ p ∈ region,
      SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
        K.roofHeight p :=
  K.exists_completionMesh_preserving_region positive small compact
    (K.combinedCompletionEquations extra) (K.combinedCompletionEquations_ne_zero extra proper)

namespace CompletionMesh

variable {K extra} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region (K.combinedCompletionEquations extra))

/-- View the unchanged actual mesh with its original-face constraints. -/
def originalConstraintView : K.CompletionMesh φ region K.originalEdgeEquations :=
  E.selectConstraints K.originalEdgeEquations Sum.inl (fun _ => rfl)

/-- View the very same actual mesh with its new cut or comparison constraints. -/
def extraConstraintView : K.CompletionMesh φ region extra :=
  E.selectConstraints extra Sum.inr (fun _ => rfl)

local instance combinedCompletionIndexFintype : Fintype E.mesh.Index :=
  @Fintype.ofFinite _ E.mesh.finite

local instance combinedOriginalViewIndexFintype :
    Fintype E.originalConstraintView.partition.Index :=
  @Fintype.ofFinite _ E.originalConstraintView.partition.finite

theorem originalConstraintView_cap : E.originalConstraintView.cap = E.cap := rfl

theorem extraConstraintView_cap : E.extraConstraintView.cap = E.cap := rfl

open Classical in
/-- The actual cut-respecting completion contains an isometric subdivision of the original roof. -/
def combinedOriginalMetricEquiv (retain : Set C.Seam) :
    E.originalConstraintView.originalComplex.Realization
      (E.originalConstraintView.originalRetain retain) ≃ᵢ C.Realization retain :=
  E.originalConstraintView.originalMetricEquiv retain

end CompletionMesh
end Unfoldings.ConvexRoof
