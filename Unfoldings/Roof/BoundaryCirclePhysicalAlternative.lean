module

public import Unfoldings.Roof.BoundaryCircleContactAlternative

/-! A coherent shared-ray circle contact retains its actual physical point equality. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem boundary_circle_physical_contact_or_common_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (leaf_coherent : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {calibration otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : FiveSector}
    {S T : MonotoneStrip} {ε δ cutoff radius : ℝ}
    (data : R.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : R.RadialStripTraceData positive small D otherCalibration j T δ cutoff)
    (H : MonotoneHeightGraph) (wall : H = T.lower ∨ H = T.upper)
    (upper : Bool) {z : ℂ} {a b : ℝ}
    (first : z ∈ closure data.strictDomain)
    (last : H.point b ∈ closure other.strictDomain)
    (height_positive : 0 < a) (ordered : a ≤ b) (before : b < cutoff)
    (radius_positive : 0 < radius)
    (first_radius : ‖data.value z - data.center‖ = radius)
    (last_radius : ‖other.value (H.point b) - other.center‖ = radius)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (contact : (fiveSectorFrame t positive small i).place.symm z =
      (fiveSectorFrame t positive small j).place.symm (H.point a))
    (first_root : H.point a =
      (if upper then (fiveSectorFrame t positive small j).enclosingStrip.upper
        else (fiveSectorFrame t positive small j).enclosingStrip.lower).point a)
    (last_root : H.point b =
      (if upper then (fiveSectorFrame t positive small j).enclosingStrip.upper
        else (fiveSectorFrame t positive small j).enclosingStrip.lower).point b) :
    ((fiveSectorFrame t positive small i).place.symm z =
        (fiveSectorFrame t positive small j).place.symm (H.point b) ∧
      data.outputFrame.symm (data.value z) = other.outputFrame.symm (other.value (H.point b))) ∨
      ∃ c : F.Component,
        origin + (fiveSectorFrame t positive small i).place.symm z ∈
          (F.componentTail c).carrier ∧
        origin + (fiveSectorFrame t positive small j).place.symm (H.point b) ∈
          (F.componentTail c).carrier ∧
        ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
          M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  let frame := fiveSectorFrame t positive small j
  let J := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  let x := origin + (fiveSectorFrame t positive small i).place.symm z
  let y := origin + frame.place.symm (H.point b)
  have boundary : ∀ k, x - origin ∉ strictFiveSector t k := by
    dsimp only [x]
    rw [add_sub_cancel_left, contact, first_root]
    have banks := fiveSector_enclosingStrip_bank_not_strict_any positive small j height_positive.le
    cases upper
    · exact banks.1
    · exact banks.2
  rcases M.sector_boundary_coherent_or_skirt positive small F covered R D leaf_coherent
    boundary with coherent | ⟨c, member⟩
  · have matching := data.circle_bank_endpoint_eq_of_earlier_coherent_contact other H wall
      first last ⟨height_positive.le, ordered⟩ radius_positive first_radius last_radius
      contact coherent
    exact Or.inl ⟨by simpa only [matching.1] using contact, matching.2⟩
  · right
    have unattached := M.sector_boundary_component_unattached positive small F covered member
      boundary
    have cone : x - origin ∈ closedFiveSector t j := by
      dsimp only [x]
      rw [add_sub_cancel_left, contact, first_root]
      have banks := fiveSector_enclosingStrip_bank_closed positive small j height_positive.le
      cases upper
      · exact banks.1
      · exact banks.2
    have cutoff_positive : 0 < cutoff := height_positive.trans_le ordered |>.trans before
    have tip_height := sector_radial_tail_tip_height_beyond positive small (F.componentTail c)
      cutoff_positive deep j member cone
    let height : Plane →ₗ[ℝ] ℝ :=
      (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.place.toLinearMap
    have x_height : height (x - origin) = a := by
      change (frame.place (x - origin)).re +
        (frame.place (x - origin)).im = a
      dsimp only [x]
      rw [add_sub_cancel_left, contact, frame.place.apply_symm_apply, H.point_height]
    have y_height : height (y - origin) = b := by
      change (frame.place (y - origin)).re +
        (frame.place (y - origin)).im = b
      dsimp only [y]
      rw [add_sub_cancel_left, frame.place.apply_symm_apply, H.point_height]
    have homogeneous : J.point b = (b / a) • J.point a := by
      have product : b / a * a = b := div_mul_cancel₀ _ height_positive.ne'
      apply (congrArg J.point product.symm).trans
      cases upper
      · exact frame.enclosingStrip_lower_point_smul
          (div_nonneg (height_positive.le.trans ordered) height_positive.le) height_positive.le
      · exact frame.enclosingStrip_upper_point_smul
          (div_nonneg (height_positive.le.trans ordered) height_positive.le) height_positive.le
    have scale : y - origin = (b / a) • (x - origin) := by
      dsimp only [x, y]
      rw [add_sub_cancel_left, add_sub_cancel_left, contact, first_root, last_root]
      change frame.place.symm (J.point b) = (b / a) • frame.place.symm (J.point a)
      rw [homogeneous, map_smul]
    have last_member := (F.componentTail c).mem_of_scaled_position_of_linear_height height
      (cutoff_positive.trans tip_height) member scale
      (by rw [x_height, y_height]; exact ordered)
      (by rw [y_height]; exact before.le.trans tip_height.le)
    exact ⟨c, member, last_member, unattached⟩

end Unfoldings.ConvexRoof.SectorForest
