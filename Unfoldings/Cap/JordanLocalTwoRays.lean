module

public import Unfoldings.Cap.JordanLocalSection
public import Unfoldings.Geometry.LocalTwoRays

/-! Actual Jordan banks follow the original two incident positive directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Local two-ray geometry of the actual curve determines a positive outgoing bank ray,
including a straight subdivided hinge. -/
theorem jordan_bank_direction_of_local_two_rays
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ) (first last : Plane)
    (locally : ∀ᶠ x in 𝓝
      (Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p)),
      x ∈ J → x - Cap.horizontal
        ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p) ∈
          nonnegativeRay first ∪ nonnegativeRay last) :
    (∃ a : ℝ, 0 < a ∧ Cap.horizontal
      ((K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val) = a • first) ∨
    (∃ b : ℝ, 0 < b ∧ Cap.horizontal
      ((K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val) = b • last) := by
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  have genuine : Cap.horizontal (F.germDirection p.val) ≠ 0 := by
    let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ p) := ⟨p.val, rfl⟩
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    exact ray
  apply exists_pos_smul_of_locally_in_two_rays _ _ first last J genuine _ locally
  intro t member
  have on_curve := (K.jordan_bankBoundary_iff jordan contains avoids
    (R.directedBoundaryPath p ⟨t, member⟩)).mp (R.directedBoundaryPath_mem_boundary _ _)
  rw [K.restrictProjection_directedBoundaryPath] at on_curve
  exact on_curve

end Unfoldings.ConvexCap
