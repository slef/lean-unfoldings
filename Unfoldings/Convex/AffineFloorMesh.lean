module

public import Unfoldings.Convex.AffineFloorSection
public import Unfoldings.Geometry.SpatialEnvelopeTriangles
public import Unfoldings.Geometry.SpatialGraphPartition

/-! A conforming affine-floor mesh retains the exact physical supporting planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane)
  (floor : Plane →ᵃ[ℝ] ℝ) (extra : J → Plane →ᵃ[ℝ] ℝ)

/-- A triangulation aligned to prescribed lines in a tilted planar section of a roof. -/
structure FloorMesh (Z : ℝ) where
  Index : Type u
  finite : Finite Index
  projectedTriangle : Index → Triangle
  support : Index → I
  cover : clipAbove family floor Z = ⋃ i, (projectedTriangle i).carrier
  separated : Pairwise (fun i j =>
    Disjoint (interior (projectedTriangle i).carrier) (interior (projectedTriangle j).carrier))
  conforming : TriangleFamily.Conforming projectedTriangle
  active : ∀ i x, x ∈ (projectedTriangle i).carrier →
    height family x = (family (support i)).height x
  sign : Index → J → Bool
  alignment : ∀ i x, x ∈ (projectedTriangle i).carrier → ∀ j,
    0 ≤ AffineArrangement.signed (extra j) (sign i j) x

/-- Use the shifted affine arrangement only to delimit the footprint. The active
support of each projected triangle determines its original spatial placement. -/
def floorMesh [Finite J] (proper : ∀ j, extra j ≠ 0) {Z : ℝ}
    (compact : IsCompact (clipAbove family floor Z)) {q : Plane}
    (above : Z + floor q < height family q) : FloorMesh family floor extra Z :=
  Classical.choice (by
    let shifted (i : I) := (family i).height - floor
    have strict : Z < AffineEnvelope.height shifted q := by
      rw [AffineEnvelope.height_sub_floor]
      exact lt_sub_iff_add_lt.mpr above
    obtain ⟨A, finite, triangles, support, signs, cover, separated, active, constrained⟩ :=
      AffineEnvelope.exists_constrained_triangle_partition shifted extra proper compact strict
    let : Finite A := finite
    let R := commonTriangleRefinement triangles
    refine ⟨{
      Index := R.Index
      finite := inferInstance
      projectedTriangle := R.triangle
      support i := support i.1
      cover := cover.trans R.total_cover
      separated := R.separated separated
      conforming := R.conforming separated
      active i x member :=
        (AffineEnvelope.active_sub_floor_iff (fun j => (family j).height) floor).mp
          (active i.1 x (R.triangle_subset i member))
      sign i := signs i.1
      alignment i x member := constrained i.1 x (R.triangle_subset i member) }⟩)

namespace FloorMesh

variable {family floor extra} {Z : ℝ} (T : FloorMesh family floor extra Z)

local instance floorMeshIndexFinite : Finite T.Index := T.finite

/-- Its physical patch is described by the old Euclidean face frames and original height. -/
def graphPartition : SpatialGraphPartition (height family) (clipAbove family floor Z) T.Index where
  footprint i := (T.projectedTriangle i).carrier
  plane i := family (T.support i)
  closed i := (T.projectedTriangle i).compact_carrier.isClosed
  convex i := (T.projectedTriangle i).convex_carrier
  full i := (T.projectedTriangle i).interior_nonempty
  disjoint _ _ ne := T.separated ne
  cover := T.cover
  active := T.active

/-- The real closed triangle in its original physical supporting frame. -/
def triangle (i : T.Index) : Triangle :=
  (T.projectedTriangle i).affineImage (family (T.support i)).project.symm.toAffineMap
    (family (T.support i)).project.symm.injective

theorem triangle_carrier (i : T.Index) : (T.triangle i).carrier =
    (family (T.support i)).project.symm '' (T.projectedTriangle i).carrier :=
  (T.projectedTriangle i).affineImage_carrier _ _

def placement (i : T.Index) : Plane →ᵃⁱ[ℝ] Space := (family (T.support i)).place

theorem placement_eq_point (i : T.Index) {x : Plane} (member : x ∈ (T.triangle i).carrier) :
    T.placement i x = point family ((family (T.support i)).project x) := by
  rw [T.triangle_carrier] at member
  obtain ⟨p, member, rfl⟩ := member
  rw [(family (T.support i)).project.apply_symm_apply]
  exact (point_eq_place family (T.support i) (T.active i p member)).symm

end FloorMesh
end Unfoldings.SpatialEnvelope
