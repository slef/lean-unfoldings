module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall
public import Unfoldings.Metric.CenteredBallRestriction
public import Unfoldings.Metric.PolygonalConvexChart

/-! Exact halfplane metric charts for the actual original one-sided roof banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The actual support-side halfplane in the anchor's original rigid coordinates. -/
def faceSideHalfspace (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool) : Set Plane :=
  {z | 0 ≤ AffineArrangement.signed f (signs anchor) ((family (P.support anchor)).project z)}

omit [Finite A] in
theorem convex_faceSideHalfspace (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool) :
    Convex ℝ (P.faceSideHalfspace anchor f signs) :=
  (convex_Ici (0 : ℝ)).affine_preimage
    ((AffineArrangement.signed f (signs anchor)).comp
      (family (P.support anchor)).project.toAffineMap)

omit [Finite A] in
theorem mem_faceSidePlanarRegion_iff (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool)
    (z : Plane) :
    z ∈ (family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs ↔
      height family ((family (P.support anchor)).project z) =
        (family (P.support anchor)).height ((family (P.support anchor)).project z) ∧
      z ∈ P.faceSideHalfspace anchor f signs := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [(family (P.support anchor)).project.apply_symm_apply]
    refine ⟨(AffineEnvelope.mem_cell_iff _ _ _).mp hp.1, ?_⟩
    change 0 ≤ AffineArrangement.signed f (signs anchor)
      ((family (P.support anchor)).project ((family (P.support anchor)).project.symm p))
    rw [(family (P.support anchor)).project.apply_symm_apply]
    exact hp.2
  · rintro ⟨active, on_side⟩
    change 0 ≤ AffineArrangement.signed f (signs anchor)
      ((family (P.support anchor)).project z) at on_side
    exact ⟨(family (P.support anchor)).project z,
      ⟨(AffineEnvelope.mem_cell_iff _ _ _).mpr active, on_side⟩,
      (family (P.support anchor)).project.symm_apply_apply z⟩

omit [Finite A] in
theorem exists_affine_preimage_ball_radius (e : Plane →ᵃ[ℝ] Plane) (p : Plane)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z p < ε → dist (e z) (e p) < δ := by
  exact Metric.continuousAt_iff.mp e.continuous_of_finiteDimensional.continuousAt δ positive

omit [Finite A] in
/-- The original geometric face germ gives the exact halfplane germ in rigid coordinates. -/
theorem exists_faceSideHalfspace_germ (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool)
    (p : Plane)
    {δ : ℝ} (positive : 0 < δ)
    (local_face : ∀ z, dist z (Cap.horizontal ((family (P.support anchor)).place p)) < δ →
      0 ≤ AffineArrangement.signed f (signs anchor) z →
        height family z = (family (P.support anchor)).height z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z p < ε →
      (z ∈ (family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs ↔
        z ∈ P.faceSideHalfspace anchor f signs) := by
  let Q := family (P.support anchor)
  obtain ⟨ε, εpos, near⟩ := exists_affine_preimage_ball_radius Q.project.toAffineMap p positive
  refine ⟨ε, εpos, ?_⟩
  intro z close
  apply (P.mem_faceSidePlanarRegion_iff anchor f signs z).trans
  constructor
  · exact And.right
  · intro on_side
    have distance : dist (Q.project z) (Q.project p) < δ :=
      near z close
    have horizontal : Cap.horizontal (Q.place p) = Q.project p :=
      Q.horizontal_place p
    have close_roof : dist (Q.project z) (Cap.horizontal (Q.place p)) < δ :=
      lt_of_eq_of_lt (congrArg (dist (Q.project z)) horizontal) distance
    exact ⟨local_face (Q.project z) close_roof on_side, on_side⟩

/-- A whole bank ball is exactly a whole ball in the original rigid halfplane.
All incident supports, copy preservation and ball coverage follow from the local geometry. -/
theorem exists_faceSideHalfspace_ball_chart (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)
    (source : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs))
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    (inside : Cap.horizontal ((family (P.support anchor)).place source.val) ∈ U)
    {δ : ℝ} (positive : 0 < δ)
    (local_face : ∀ z, dist z (Cap.horizontal ((family (P.support anchor)).place source.val)) < δ →
      0 ≤ AffineArrangement.signed f (signs anchor) z →
        height family z = (family (P.support anchor)).height z) :
    ∃ r : ℝ, 0 < r ∧ ∃ a : P.faceSideHalfspace anchor f signs, a.val = source.val ∧
      ∃ B : Metric.eball
        (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source)
          (ENNReal.ofReal r) ≃ᵢ Metric.ball a r,
        ∀ y, (family (P.support anchor)).place (B y).val.val = (P.restoreCut cuts y.val).val := by
  obtain ⟨r, rpos, B, agrees⟩ := P.exists_faceSideRegionMap_ball_chart anchor f proper signs aligned
    cuts cut_closed cut_level source open_U cut_line inside positive local_face
  obtain ⟨ε, εpos, local_eq⟩ := P.exists_faceSideHalfspace_germ
    anchor f signs source.val positive local_face
  let radius := min r ε
  have radius_pos : 0 < radius := lt_min rpos εpos
  have big_positive := ENNReal.ofReal_pos.mpr rpos
  let small := ENNReal.ofReal_le_ofReal (min_le_left r ε)
  have center : (B ⟨source, Metric.mem_eball_self big_positive⟩).val =
      P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source := agrees _
  let C := restrictCenteredEBallEquiv big_positive small B center
  have agrees_small (z : Metric.eball source (ENNReal.ofReal radius)) :
      (C z).val =
        P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level z.val :=
    (restrictCenteredEBallEquiv_val big_positive small B center z).trans (agrees _)
  let a : P.faceSideHalfspace anchor f signs :=
    ⟨source.val, ((P.mem_faceSidePlanarRegion_iff anchor f signs source.val).mp source.property).2⟩
  obtain ⟨D, coordinates⟩ := PolygonalPoint.exists_local_convex_ball_isometry
    source a rfl radius_pos
    (P.convex_faceSideHalfspace anchor f signs)
    (fun z close => local_eq z (close.trans_le (min_le_right r ε)))
  refine ⟨radius, radius_pos, a, rfl, C.symm.trans D, ?_⟩
  intro y
  let z := C.symm y
  have image : P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level z.val =
      y.val := (agrees_small z).symm.trans (congrArg Subtype.val (C.apply_symm_apply y))
  change (family (P.support anchor)).place (D z).val.val = _
  calc
    _ = (family (P.support anchor)).place z.val.val := congrArg _ (coordinates z)
    _ = (P.restoreCut cuts
      (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level z.val)).val :=
        (P.restoreCut_faceSideRegionMap anchor f proper signs aligned
          cuts cut_closed cut_level z.val).symm
    _ = (P.restoreCut cuts y.val).val := congrArg (fun w => (P.restoreCut cuts w).val) image

end Unfoldings.SpatialEnvelope.WholePartition
