module

public import Unfoldings.Cap.ComponentBankCircleContact
public import Unfoldings.Cap.ClosedStripCircleCaps
public import Unfoldings.Cap.ClosedCircleBankCoordinates
public import Unfoldings.Cap.ClosedBarrierContact
public import Unfoldings.Cap.CompletedBankClosedContact
public import Unfoldings.Cap.ChainWeakCircleContact

/-! Closed trace contacts across a component identify their actual physical bank endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (e f : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
  (c : F.Component)
  (unattached : ∀ a : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl a) ≠ c)
  (first : Q.projectedVertex e.val ∈ (F.componentTail c).carrier)
  (last : Q.projectedVertex f.val ∈ (F.componentTail c).carrier)

include lower unattached first last

/-- The weak circle comparison is applied to the actual approached strip traces in
possibly different sector frames. It identifies both physical endpoint coordinates. -/
theorem closed_circle_contact_preimages_of_component_bank_bounds
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t l)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (s r : unitInterval) {radius : ℝ}
    (exit_inside : ‖R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin)‖ ≤ radius)
    (entrance_inside :
      ‖R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin)‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
        0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin))).im) ∧
      (0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
        0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
          D.projectedMap Q (K.projectedVertex origin))).im))
    {S T : MonotoneStrip} {ε cutoff : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) l T ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (first_bound_le : (data.value (S.upper.point slice.upperHeight) - data.center).re ≤
      (B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin))).re)
    (last_bound_le : (other.value (T.lower.point other_slice.lowerHeight) - other.center).im ≤
      (B.sectorFrame l (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin))).im)
    {x y : ℂ} (first_closed : x ∈ closure (S.openSlab 0 cutoff))
    (last_closed : y ∈ closure (T.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius)
    (same : data.outputFrame.symm (data.value x) = other.outputFrame.symm (other.value y)) :
    x = S.upper.point slice.upperHeight ∧ y = T.lower.point other_slice.lowerHeight ∧
      AffineMap.lineMap (Q.projectedVertex e.val)
        (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) =
      AffineMap.lineMap (Q.projectedVertex f.val)
        (Q.projectedVertex (R.spanningCompletion.parents.parent f.val)) (r : ℝ) := by
  let p := data.outputFrame.symm (data.value x)
  have other_size : ‖other.value y - other.center‖ = radius := by
    rw [← other.outputFrame_symm_source_distance, ← same,
      data.outputFrame_symm_source_distance]
    exact size
  have first_caps := B.closed_circle_image_subset_weak_caps i data slice first_order first_error
    first_margin radius_positive far ⟨data.value x, ⟨⟨x, first_closed, rfl⟩, size⟩, rfl⟩
  have last_caps := B.closed_circle_image_subset_weak_caps l other other_slice last_order last_error
    last_margin radius_positive far ⟨other.value y, ⟨⟨y, last_closed, rfl⟩, other_size⟩, same.symm⟩
  have contact := M.weak_circle_caps_contact_values_of_component_bank_bounds F covered lower R
    e f c unattached first last positive small outward footprint i l first_inside last_inside
    curvature_covered D B budget s r (D.projectedMap Q (K.projectedVertex origin))
    exit_inside entrance_inside quadrants first_bound_le last_bound_le ⟨first_caps.1, last_caps.2⟩
  have first_centered : B.sectorFrame i (p - D.projectedMap Q (K.projectedVertex origin)) =
      data.value x - data.center := by
    change data.outputFrame (data.outputFrame.symm (data.value x) -
      D.projectedMap Q (K.projectedVertex origin)) = _
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← data.center_eq_outputFrame]
  have last_centered : B.sectorFrame l (p - D.projectedMap Q (K.projectedVertex origin)) =
      other.value y - other.center := by
    change other.outputFrame (data.outputFrame.symm (data.value x) -
      D.projectedMap Q (K.projectedVertex origin)) = _
    rw [same, map_sub, LinearIsometryEquiv.apply_symm_apply, ← other.center_eq_outputFrame]
  have upper_bound := first_bound_le
  rw [← contact.1] at upper_bound
  have horizontal := le_antisymm first_caps.1.2.2.1 upper_bound
  rw [first_centered] at horizontal
  have entrance : p = R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) :=
    contact.1.trans contact.2
  have lower_bound := last_bound_le
  rw [← entrance] at lower_bound
  have vertical := le_antisymm last_caps.2.2.2.1 lower_bound
  rw [last_centered] at vertical
  have first_subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_subset : T.openSlab 0 cutoff ⊆ other.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  exact ⟨data.closed_circle_point_eq_upper_of_horizontal_eq slice first_error first_margin
      radius_positive (closure_mono first_subset first_closed) size horizontal,
    other.closed_circle_point_eq_lower_of_vertical_eq other_slice last_error last_margin
      radius_positive (closure_mono last_subset last_closed) other_size vertical,
    M.unattached_component_bank_contact_same_projected_point F covered lower R e f c
      unattached first last positive small outward footprint i first_inside
      curvature_covered D B budget s r contact.2⟩

end Unfoldings.ConvexCap.SectorForest
