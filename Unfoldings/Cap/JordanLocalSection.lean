module

public import Unfoldings.Cap.RestrictedBankSegments
public import Unfoldings.Cap.JordanSectionSet
public import Unfoldings.Geometry.LocalLineSegment

/-! Local straightness of the actual Jordan boundary forces opposite original bank directions. -/

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
/-- Every actual bank incident at a locally straight boundary point lies on its genuine line. -/
theorem jordan_bank_direction_of_local_line
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ) (direction : Plane)
    (locally : ∀ᶠ x in 𝓝
      (Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p)),
      x ∈ J → ∃ a : ℝ, x =
        Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p) +
          a • direction) :
    ∃ a : ℝ, Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val) =
      a • direction := by
  apply exists_smul_of_locally_in_line _ _ direction J _ locally
  intro t member
  let s : unitInterval := ⟨t, member⟩
  have on_curve := (K.jordan_bankBoundary_iff jordan contains avoids
    ((C.restrictFaces (K.jordanFaces J)).directedBoundaryPath p s)).mp
      ((C.restrictFaces (K.jordanFaces J)).directedBoundaryPath_mem_boundary p s)
  rw [K.restrictProjection_directedBoundaryPath] at on_curve
  exact on_curve

include jordan contains avoids in
open Classical in
/-- Opposite direction is proved from actual bank separation, without a supplied angle test. -/
theorem jordan_bank_rays_of_local_line
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ)
    (direction : Plane) (nonzero : direction ≠ 0)
    (locally : ∀ᶠ x in 𝓝
      (Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p)),
      x ∈ J → ∃ a : ℝ, x =
        Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition p) +
          a • direction) :
    ∃ a b : ℝ, a * b < 0 ∧
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val) =
        a • direction ∧
      Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).germDirection
        ((C.restrictFaces (K.jordanFaces J)).boundaryMate Set.univ p).val) = b • direction := by
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  have locally_q : ∀ᶠ x in 𝓝 (Cap.horizontal (F.boundaryPosition q)),
      x ∈ J → ∃ a : ℝ, x = Cap.horizontal (F.boundaryPosition q) + a • direction := by
    have same : F.boundaryPosition q = F.boundaryPosition p := F.boundaryPosition_mate p
    rw [same]
    exact locally
  obtain ⟨a, outgoing⟩ := K.jordan_bank_direction_of_local_line jordan contains avoids p direction
    locally
  obtain ⟨b, incoming⟩ := K.jordan_bank_direction_of_local_line jordan contains avoids q direction
    locally_q
  have genuine (bank : R.BoundaryEnd Set.univ) : Cap.horizontal (F.germDirection bank.val) ≠ 0 := by
    let g : R.LinkGerm Set.univ (R.boundaryEndVertex Set.univ bank) := ⟨bank.val, rfl⟩
    have ray := K.projectedGermRay_ne_zero (C.includeRestrictedLinkGerm U g)
    rw [← K.horizontal_germDirection] at ray
    exact ray
  have an : a ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at outgoing
    exact genuine p outgoing
  have bn : b ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at incoming
    exact genuine q incoming
  have separated := K.restricted_boundary_rays_angle_ne_zero U p
  rw [outgoing, incoming] at separated
  refine ⟨a, b, ?_, outgoing, incoming⟩
  by_contra not_negative
  have positive : 0 < a * b := lt_of_le_of_ne (le_of_not_gt not_negative)
    (mul_ne_zero an bn).symm
  rcases mul_pos_iff.mp positive with ⟨ap, bp⟩ | ⟨an, bn⟩
  · rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ap,
      InnerProductGeometry.angle_smul_right_of_pos _ _ bp,
      InnerProductGeometry.angle_self nonzero] at separated
    exact separated rfl
  · rw [InnerProductGeometry.angle_smul_left_of_neg _ _ an,
      InnerProductGeometry.angle_smul_right_of_neg _ _ bn,
      InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_self nonzero] at separated
    exact separated rfl


include jordan contains avoids in
open Classical in
/-- Local straightness along one actual line gives the full error bound for any selected set. -/
theorem sum_abs_jordan_locally_straight_error_le_tilt (inside : J ⊆ interior K.footprint)
    (selected : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1)))
    (origin direction : Plane) (unit : ‖direction‖ = 1)
    (locally : ∀ i ∈ selected, ∀ᶠ x in 𝓝
      (Cap.horizontal ((K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition
        ((K.jordanContour jordan contains avoids).cycle.point i))),
      x ∈ J → ∃ a : ℝ, x = origin + a • direction)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i ∈ selected, |K.jordanContourTurnError jordan contains avoids i|) ≤ 2 * φ := by
  let U := K.jordanFaces J
  let R := C.restrictFaces U
  let F := K.folding.restrictFaces U
  let Q := K.jordanContour jordan contains avoids
  have on_curve (i : Fin (Q.length + 1)) :
      Cap.horizontal (F.boundaryPosition (Q.cycle.point i)) ∈ J := by
    have member := (K.jordan_isBoundaryVertex_iff jordan contains avoids
      (R.boundaryEndVertex Set.univ (Q.cycle.point i))).mp
        (R.boundaryEndAsVertex Set.univ (Q.cycle.point i)).property
    rw [K.projected_restricted_boundaryPosition U] at member
    exact member
  have collinear (i) (member : i ∈ selected) : ∃ a : ℝ,
      Cap.horizontal (F.boundaryPosition (Q.cycle.point i)) = origin + a • direction :=
    (locally i member).self_of_nhds (on_curve i)
  have nonzero : direction ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  apply K.sum_abs_jordan_section_set_error_le_tilt jordan contains avoids inside selected
    origin direction unit collinear _ nonnegative small tilt
  intro i member
  apply K.jordan_bank_rays_of_local_line jordan contains avoids (Q.cycle.point i) direction
    nonzero
  obtain ⟨s, at_base⟩ := collinear i member
  filter_upwards [locally i member] with x near
  intro onJ
  obtain ⟨t, at_x⟩ := near onJ
  refine ⟨t - s, ?_⟩
  rw [at_x, at_base]
  module

end Unfoldings.ConvexCap
