module

public import Unfoldings.Roof.RadialComponentCommonChain
public import Unfoldings.Cap.CrossFrameStripCircleBounds

/-! Actual radial-component banks separate outward circle arcs in neighboring frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (e f : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
  (c : F.Component)
  (unattached : ∀ a : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl a) ≠ c)
  (first : Q.projectedVertex e.val ∈ (F.componentTail c).carrier)
  (last : Q.projectedVertex f.val ∈ (F.componentTail c).carrier)

include unattached first last

theorem circle_arcs_disjoint_of_component_bank_bounds
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t l)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (s r : unitInterval) (center : Plane) {radius : ℝ}
    (exit_inside : ‖R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center‖ ≤ radius)
    (entrance_inside :
      ‖R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).im) ∧
      (0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im))
    {A E : Set Plane}
    (first_bounds : ∀ p ∈ A, 0 ≤ (B.sectorFrame i (p - center)).re ∧
      0 < (B.sectorFrame i (p - center)).im ∧
      (B.sectorFrame i (p - center)).re <
        (B.sectorFrame i
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re)
    (last_bounds : ∀ p ∈ E, 0 ≤ (B.sectorFrame l (p - center)).re ∧
      0 < (B.sectorFrame l (p - center)).im ∧
      (B.sectorFrame l (p - center)).im <
        (B.sectorFrame l
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im)
    (first_radius : ∀ p ∈ A, ‖p - center‖ = radius)
    (last_radius : ∀ p ∈ E, ‖p - center‖ = radius) : Disjoint A E := by
  have comparison := M.unattached_component_bank_points_cross_frame_alternative F covered
    R e f c unattached first last positive small outward footprint i l first_inside last_inside
    curvature_covered D B budget s r center
  apply Set.disjoint_left.mpr
  intro p member other_member
  have left := first_bounds p member
  have right := last_bounds p other_member
  rcases comparison with horizontal | vertical
  · exact B.inner_barrier_point_exclusion_of_norm_le i l center
      (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ))) p
      (quadrants i (Or.inl rfl)).2 (quadrants l (Or.inr rfl)).2
      ⟨left.1, left.2.1⟩ ⟨right.1, right.2.1⟩
      (left.2.2.trans_le horizontal) right.2.2
      (entrance_inside.trans_eq (first_radius p member).symm)
  · exact B.inner_barrier_point_exclusion_of_norm_le i l center
      (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))) p
      (quadrants i (Or.inl rfl)).1 (quadrants l (Or.inr rfl)).1
      ⟨left.1, left.2.1⟩ ⟨right.1, right.2.1⟩
      left.2.2 (right.2.2.trans_le vertical)
      (exit_inside.trans_eq (last_radius p other_member).symm)

/-- Apply component-derived bank comparison to actual waterfall trace images.
The only coordinate bounds concern each strip's own named terminal or circle
candidate. The common fine path and both sector geometries are constructed. -/
theorem circle_images_disjoint_of_component_bank_bounds
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t l)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
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
    (radius_positive : 0 < radius)
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (s r : unitInterval)
    (exit_inside : ‖R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
      D.projectedMap Q (origin)‖ ≤ radius)
    (entrance_inside : ‖R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
      D.projectedMap Q (origin)‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
          D.projectedMap Q (origin))).re ∧
        0 < (B.sectorFrame a (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
          D.projectedMap Q (origin))).im) ∧
      (0 < (B.sectorFrame a (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
          D.projectedMap Q (origin))).re ∧
        0 < (B.sectorFrame a (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
          D.projectedMap Q (origin))).im))
    (first_bound : (data.value (S.upper.point slice.upperHeight) - data.center).re ≤
      (B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
        D.projectedMap Q (origin))).re)
    (last_bound : (other.value (T.lower.point other_slice.lowerHeight) - other.center).im ≤
      (B.sectorFrame l (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
        D.projectedMap Q (origin))).im) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have first_bounds := fun {p : Plane} => B.circle_image_open_bank_bounds i data slice first_order
    first_error first_margin radius_positive (p := p)
  have last_bounds := fun {p : Plane} =>
    B.circle_image_open_bank_bounds l other other_slice last_order
      last_error last_margin radius_positive (p := p)
  apply M.circle_arcs_disjoint_of_component_bank_bounds F covered R e f c unattached
    first last positive small outward footprint i l first_inside last_inside curvature_covered
    D B budget s r (D.projectedMap Q (origin)) exit_inside entrance_inside
    quadrants
  · intro p member
    have bounds := first_bounds member
    exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.1.trans_le first_bound⟩
  · intro p member
    have bounds := last_bounds member
    exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.2.1.trans_le last_bound⟩
  · intro p member
    exact (first_bounds member).2.2.2.2
  · intro p member
    exact (last_bounds member).2.2.2.2

end Unfoldings.ConvexRoof.SectorForest
