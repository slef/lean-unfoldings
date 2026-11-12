module

public import Unfoldings.Cap.ComponentBankCircleCaps
public import Unfoldings.Cap.ClosedBarrierContact
public import Unfoldings.Cap.CompletedBankClosedContact
public import Unfoldings.Cap.ChainWeakCircleContact

/-! Any weak circle contact across actual skirt-component banks is an actual named bank point. -/

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

theorem weak_circle_caps_contact_of_component_bank_bounds
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t l)
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
    {first_bound last_bound : ℝ}
    (first_bound_le : first_bound ≤ (B.sectorFrame i
      (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re)
    (last_bound_le : last_bound ≤ (B.sectorFrame l
      (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im) :
    weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
        weakCircleLowerCap (B.sectorFrame l) center radius last_bound ⊆
      {R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)),
        R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ))} := by
  apply B.weak_circle_caps_inter_subset_bank_points i l center _ _ radius first_bound last_bound
    exit_inside entrance_inside quadrants first_bound_le last_bound_le
  exact M.unattached_component_bank_points_cross_frame_alternative F covered lower R e f c
    unattached first last positive small outward footprint i l first_inside last_inside
    curvature_covered D B budget s r center

/-- Closed contacts of actual banks on one unattached radial component have the same
physical projection, including contacts at either endpoint of an edge. -/
theorem unattached_component_bank_contact_same_projected_point
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i : FiveSector)
    (inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t i)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (s r : unitInterval)
    (same : R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) =
      R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ))) :
    AffineMap.lineMap (Q.projectedVertex e.val)
      (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) =
    AffineMap.lineMap (Q.projectedVertex f.val)
      (Q.projectedVertex (R.spanningCompletion.parents.parent f.val)) (r : ℝ) := by
  obtain ⟨w, j, k, left, right, geometry⟩ := M.unattached_component_common_bank_chain_geometry F
    covered lower R e f c unattached first last positive small outward footprint i i
    inside inside curvature_covered
  have contact := B.chain_contact_same_projected_point i (R.completedBankChain w)
    (R.completedBankChain_parent w) (geometry i (Or.inl rfl)).1
    (geometry i (Or.inl rfl)).2 budget j k s r (by simpa only [left, right] using same)
  simpa only [left, right] using contact

/-- Circle contact across actual component banks identifies one physical surface point. -/
theorem weak_circle_caps_contact_same_projected_point
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
    (s r : unitInterval) (center : Plane) {radius : ℝ}
    (exit_radius : ‖R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center‖ = radius)
    (entrance_radius :
      ‖R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center‖ = radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).im) ∧
      (0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).re ∧
        0 < (B.sectorFrame a
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im))
    {first_bound last_bound : ℝ}
    (first_bound_le : first_bound ≤ (B.sectorFrame i
      (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re)
    (last_bound_le : last_bound ≤ (B.sectorFrame l
      (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im)
    {p : Plane} (member : p ∈
      weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
        weakCircleLowerCap (B.sectorFrame l) center radius last_bound) :
    p = R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) ∧
      AffineMap.lineMap (Q.projectedVertex e.val)
        (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) =
      AffineMap.lineMap (Q.projectedVertex f.val)
        (Q.projectedVertex (R.spanningCompletion.parents.parent f.val)) (r : ℝ) := by
  have contact := B.weak_circle_caps_contact_eq i l center _ _ radius first_bound last_bound
    exit_radius entrance_radius quadrants first_bound_le last_bound_le
    (M.unattached_component_bank_points_cross_frame_alternative F covered lower R e f c
      unattached first last positive small outward footprint i l first_inside last_inside
      curvature_covered D B budget.le s r center) member
  exact ⟨contact.1, M.unattached_component_bank_contact_same_projected_point F covered lower R
    e f c unattached first last positive small outward footprint i first_inside
    curvature_covered D B budget s r contact.2⟩

/-- No common-radius hypothesis on the comparison banks is needed to identify their
physical points at a weak circle contact. -/
theorem weak_circle_caps_contact_physical_eq
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - K.projectedVertex origin ∈ closedFiveSector t l)
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
    {first_bound last_bound : ℝ}
    (first_bound_le : first_bound ≤ (B.sectorFrame i
      (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re)
    (last_bound_le : last_bound ≤ (B.sectorFrame l
      (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im)
    {p : Plane} (member : p ∈
      weakCircleUpperCap (B.sectorFrame i) center radius first_bound ∩
        weakCircleLowerCap (B.sectorFrame l) center radius last_bound) :
    AffineMap.lineMap (Q.projectedVertex e.val)
      (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) =
    AffineMap.lineMap (Q.projectedVertex f.val)
      (Q.projectedVertex (R.spanningCompletion.parents.parent f.val)) (r : ℝ) := by
  obtain ⟨w, j, k, left, right, geometry⟩ := M.unattached_component_common_bank_chain_geometry F
    covered lower R e f c unattached first last positive small outward footprint i l
    first_inside last_inside curvature_covered
  have contact := B.chain_weak_circle_caps_contact_same_projected_point i l
    (R.completedBankChain w) (R.completedBankChain_parent w)
    (geometry i (Or.inl rfl)).1 (geometry l (Or.inr rfl)).1
    (geometry i (Or.inl rfl)).2 (geometry l (Or.inr rfl)).2 budget j k s r center
    (by simpa only [left] using exit_inside) (by simpa only [right] using entrance_inside)
    (by simpa only [left, right] using quadrants)
    (by simpa only [left] using first_bound_le) (by simpa only [right] using last_bound_le) member
  simpa only [left, right] using contact

end Unfoldings.ConvexCap.SectorForest
