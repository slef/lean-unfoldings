module

public import Unfoldings.Geometry.SpatialEnvelopeCutBanks
public import Unfoldings.Geometry.SpatialEnvelopeFaceSide
public import Unfoldings.Geometry.AffinePatch

/-! Actual metric bank classes retain their cut side and their physical supporting face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

omit [Finite A] in
/-- Each spatial cell copy projects into its actual original footprint. -/
theorem horizontal_mem_footprint_of_spatial (a : A) (z : P.spatialCell a) :
    Cap.horizontal z.val ∈ P.footprint a := by
  obtain ⟨z, x, hx, rfl⟩ := z
  exact P.horizontal_mem_footprint a ⟨x, hx⟩

omit [Finite A] in
/-- A local complete cut line preserves the physical side along each actual retained attachment. -/
theorem cutPhysicalSeams_sign_eq (cuts : Set Plane) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    {z : Space} (inside : Cap.horizontal z ∈ U) (a b : A)
    (seam : z ∈ (P.cutPhysicalSeams cuts).carrier a b) : signs a = signs b := by
  have spatial_aligned : ∀ a z, z ∈ P.spatialCell a →
      0 ≤ AffineArrangement.signed (f.comp Cap.horizontal.toAffineMap) (signs a) z := by
    intro a z hz
    have bound := aligned a (Cap.horizontal z) (P.horizontal_mem_footprint_of_spatial a ⟨z, hz⟩)
    simpa only [AffineArrangement.signed_apply, AffineMap.comp_apply, LinearMap.coe_toAffineMap]
      using bound
  exact MetricGluing.cutSeams_sign_eq P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) (f.comp Cap.horizontal.toAffineMap) signs spatial_aligned
    (open_U.preimage Cap.horizontalCLM.continuous) (fun z hz zero => cut_line _ hz zero)
    inside a b seam

/-- The whole declared metric class lies on one original side of a locally complete cut line. -/
theorem cutClass_side_eq (cuts : Set Plane) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    {a b : MetricGluing.Total (fun a => P.spatialCell a)} (inside : Cap.horizontal a.2.val ∈ U)
    (related : Relation.EqvGen (P.cutPhysicalSeams cuts).relation a b) : signs a.1 = signs b.1 :=
  (P.cutPhysicalSeams cuts).label_eq_of_eqvGen signs a.2.val
    (fun i j member => P.cutPhysicalSeams_sign_eq cuts f signs aligned open_U cut_line inside i j
      member) related rfl

/-- Every cell of the actual bank class belongs to the same complete physical face-side region.
Local geometry supplies the affine support equality; it is not assumed for incident cells. -/
theorem cutClass_mem_faceSideIndex (anchor : A) (cuts : Set Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    {a b : MetricGluing.Total (fun a => P.spatialCell a)} (inside : Cap.horizontal a.2.val ∈ U)
    (side : signs a.1 = signs anchor)
    (related : Relation.EqvGen (P.cutPhysicalSeams cuts).relation a b)
    {r : ℝ} (positive : 0 < r)
    (local_face : ∀ z, dist z (Cap.horizontal a.2.val) < r →
      0 ≤ AffineArrangement.signed f (signs anchor) z →
        height family z = (family (P.support anchor)).height z) :
    (family (P.support b.1)).height = (family (P.support anchor)).height ∧
      signs b.1 = signs anchor := by
  have bank_side := P.cutClass_side_eq cuts f signs aligned open_U cut_line inside related
  have side_b : signs b.1 = signs anchor := bank_side.symm.trans side
  refine ⟨?_, side_b⟩
  have physical := (P.cutPhysicalSeams cuts).physical_eq_of_eqvGen related
  have member : Cap.horizontal a.2.val ∈ P.footprint b.1 := by
    rw [physical]
    exact P.horizontal_mem_footprint_of_spatial b.1 b.2
  apply affine_eq_on_convex_patch (P.convex b.1) (P.full b.1) member positive
  intro z hz near
  have on_side : 0 ≤ AffineArrangement.signed f (signs anchor) z := by
    simpa only [side_b] using aligned b.1 z hz
  exact (P.active b.1 z hz).symm.trans (local_face z near on_side)

end Unfoldings.SpatialEnvelope.WholePartition
