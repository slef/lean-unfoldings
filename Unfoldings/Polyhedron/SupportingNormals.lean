module

public import Unfoldings.Polyhedron.FaceSupport
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Actual outward unit normals for every original triangle of a convex polyhedral boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- Unit normals tangent to the actual input planes and supporting the entire convex body.
No graph projection, normal selection, or disk conclusion is supplied as input. -/
structure SupportingNormals (F : SpatialFolding C) where
  normal : Face → Space
  unit : ∀ f, ‖normal f‖ = 1
  tangent : ∀ f x, inner ℝ (normal f) ((F.place f).linear x) = 0
  supporting : ∀ f z, z ∈ F.vertexHull → inner ℝ (normal f) (z - F.place f 0) ≤ 0

namespace SupportingNormals

variable {F : SpatialFolding C} (N : F.SupportingNormals)

theorem ne_zero (f : Face) : N.normal f ≠ 0 := by
  intro zero
  have unit := N.unit f
  rw [zero, norm_zero] at unit
  norm_num at unit

theorem on_plane (f : Face) (x : Plane) :
    inner ℝ (N.normal f) (F.place f x - F.place f 0) = 0 := by
  have chord := (F.place f).toAffineMap.linear_apply_vsub x 0
  change (F.place f).linear (x - 0) = F.place f x - F.place f 0 at chord
  rw [sub_zero] at chord
  rw [← chord]
  exact N.tangent f x

theorem supporting_strict (f : Face) {z : Space} (inside : z ∈ interior F.vertexHull) :
    inner ℝ (N.normal f) (z - F.place f 0) < 0 := by
  let functional := innerSL ℝ (N.normal f)
  have nonzero : functional ≠ 0 := by
    intro zero
    have value := congrArg (fun l : Space →L[ℝ] ℝ => l (N.normal f)) zero
    have norm := N.unit f
    change inner ℝ (N.normal f) (N.normal f) = 0 at value
    rw [real_inner_self_eq_norm_sq, norm] at value
    norm_num at value
  have bound : ∀ x ∈ F.vertexHull, functional x ≤ functional (F.place f 0) := by
    intro x hx
    have support := N.supporting f x hx
    rwa [inner_sub_right, sub_nonpos] at support
  have strict := supporting_functional_lt_on_interior functional nonzero F.vertexHull
    (functional (F.place f 0)) bound z inside
  change inner ℝ (N.normal f) z < inner ℝ (N.normal f) (F.place f 0) at strict
  rwa [inner_sub_right, sub_lt_zero]

end SupportingNormals

namespace ConvexBoundary

variable {F : SpatialFolding C} (P : F.ConvexBoundary)

/-- Supporting planes derived from the embedded convex boundary give outward unit normals,
including triangles subdividing a flat facet. -/
def supportingNormals : F.SupportingNormals := by
  classical
  have exists_normal (face : Face) : ∃ n : Space, ‖n‖ = 1 ∧
      (∀ x, inner ℝ n ((F.place face).linear x) = 0) ∧
      ∀ z ∈ F.vertexHull, inner ℝ n (z - F.place face 0) ≤ 0 := by
    obtain ⟨functional, level, nonzero, supporting, _strict, on_plane⟩ := P.exists_face_support face
    let n := (InnerProductSpace.toDual ℝ Space).symm functional
    have pairing (z : Space) : inner ℝ n z = functional z :=
      InnerProductSpace.toDual_symm_apply
    have nonzero_n : n ≠ 0 := by
      intro zero
      apply nonzero
      ext z
      change functional z = 0
      rw [← pairing z, zero, inner_zero_left]
    refine ⟨NormedSpace.normalize n, NormedSpace.norm_normalize nonzero_n, ?_, ?_⟩
    · intro x
      have chord : (F.place face).linear x = F.place face x - F.place face 0 := by
        have mapped := (F.place face).toAffineMap.linear_apply_vsub x 0
        change (F.place face).linear (x - 0) = F.place face x - F.place face 0 at mapped
        simpa only [sub_zero] using mapped
      change inner ℝ (‖n‖⁻¹ • n) _ = 0
      rw [real_inner_smul_left, pairing, chord, map_sub, on_plane, on_plane, sub_self, mul_zero]
    · intro z hz
      change inner ℝ (‖n‖⁻¹ • n) (z - F.place face 0) ≤ 0
      rw [real_inner_smul_left, pairing, map_sub, on_plane]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg n))
        (sub_nonpos.mpr (supporting z hz))
  choose normal unit tangent supporting using exists_normal
  exact ⟨normal, unit, tangent, supporting⟩

end ConvexBoundary
end Unfoldings.SpatialFolding
