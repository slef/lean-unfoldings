module

public import Unfoldings.Roof.CompletionPlanes
public import Unfoldings.Roof.SpatialEnvelopeCap

/-! Actual compact cap completions of arbitrary-rim roofs with prescribed mesh lines. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A conforming physical cap completion, covering the old footprint and a prescribed region.
Every extra line carries actual side data through the auxiliary triangulation. -/
structure CompletionMesh (φ : ℝ) (region : Set Plane) {J : Type u}
    (extra : J → Plane →ᵃ[ℝ] ℝ) where
  tentHeight : ℝ
  level : ℝ
  mesh : SpatialEnvelope.ConstrainedTriangulation
    (K.completionPlanes tentHeight (Real.sin φ / 2)) extra level
  conforming : TriangleFamily.Conforming mesh.projectedTriangle
  covers : K.footprint ∪ region ⊆ interior
    (SpatialEnvelope.clip (K.completionPlanes tentHeight (Real.sin φ / 2)) level)
  unchanged : ∀ p ∈ K.footprint,
    SpatialEnvelope.height (K.completionPlanes tentHeight (Real.sin φ / 2)) p = K.roofHeight p

/-- Compact original geometry, arbitrary rim heights, and any finite collection of proper
lines construct a genuine physical completion mesh. No unfolding or acute skirt is supplied. -/
theorem exists_completionMesh {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2)
    {region : Set Plane} (compact : IsCompact region) {J : Type u} [Finite J]
    (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0) :
    Nonempty (K.CompletionMesh φ region extra) := by
  let L := Real.sin φ / 2
  have Lpositive : 0 < L := tent_slope_positive positive small
  obtain ⟨H, inactive⟩ := K.exists_tent_height L
  obtain ⟨Z₀, _, deep⟩ := K.exists_deep_tentCompletionClip H L 0 (K.compact_footprint.union compact)
  let Z := Z₀ - 1
  let family := K.completionPlanes H L
  have heights (p : Plane) : SpatialEnvelope.height family p = K.tentCompletionHeight H L p :=
    K.completionPlanes_envelope H L p
  have equal_clip : SpatialEnvelope.clip family Z = K.tentCompletionClip H L Z := by
    ext p
    change (Z ≤ AffineEnvelope.height (fun i => (family i).height) p) ↔ _
    rw [K.completionPlanes_envelope]
    rfl
  have strict : ∀ p ∈ K.footprint ∪ region, Z < SpatialEnvelope.height family p := by
    intro p member
    have bound := interior_subset (deep member)
    change Z₀ ≤ K.tentCompletionHeight H L p at bound
    rw [heights]
    dsimp [Z]
    linarith
  obtain ⟨q, inside⟩ := K.interior_projection
  have higher := strict q (Or.inl (interior_subset inside))
  have compact_clip : IsCompact (SpatialEnvelope.clip family Z) := by
    rw [equal_clip]
    exact K.isCompact_tentCompletionClip H Lpositive Z
  let T := SpatialEnvelope.constrainedTriangulation family extra proper compact_clip higher
  refine ⟨{ tentHeight := H
            level := Z
            mesh := T.refined
            conforming := T.refined_conforming
            covers := fun p member =>
              AffineEnvelope.mem_interior_clip (fun i => (family i).height) (strict p member)
            unchanged := fun p member => (heights p).trans
              (K.tentCompletionHeight_eq_on_footprint Lpositive.le inactive member) }⟩

namespace CompletionMesh

variable {K} {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

local instance : Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

theorem interior_nonempty : (interior
    (SpatialEnvelope.clip (K.completionPlanes E.tentHeight
      (Real.sin φ / 2)) E.level)).Nonempty := by
  obtain ⟨q, inside⟩ := K.interior_projection
  exact ⟨q, E.covers (Or.inl (interior_subset inside))⟩

/-- The completion mesh is a genuine geometric cap in the existing cap API. -/
def cap : ConvexCap E.mesh.toTriangulation.pairedComplex :=
  E.mesh.toTriangulation.normalizedCap E.conforming E.interior_nonempty

/-- The original normal tilt budget survives the full physical cap construction. -/
theorem cap_tilt {φ : ℝ} {E : K.CompletionMesh φ region extra}
    (positive : 0 < φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) : E.cap.TiltBound φ :=
  E.mesh.toTriangulation.normalizedCap_tilt E.conforming E.interior_nonempty
    (K.completionPlanes_tilt positive small tilt E.tentHeight)

theorem cap_footprint : E.cap.footprint =
    SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level :=
  E.mesh.toTriangulation.normalizedCap_footprint E.conforming E.interior_nonempty

end CompletionMesh
end Unfoldings.ConvexRoof
