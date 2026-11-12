module

public import Unfoldings.Cap.RadialComponentCommonChain
public import Unfoldings.Geometry.CircleCoordinateCaps
public import Unfoldings.Cap.ComponentBankCircleSeparation

/-! Actual component banks separate entire coordinate-bounded circle portions. -/

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

theorem circle_caps_disjoint_of_component_bank_bounds
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
    Disjoint (circleUpperCap (B.sectorFrame i) center radius first_bound)
      (circleLowerCap (B.sectorFrame l) center radius last_bound) := by
  apply M.circle_arcs_disjoint_of_component_bank_bounds F covered lower R e f c unattached
    first last positive small outward footprint i l first_inside last_inside curvature_covered
    D B budget s r center exit_inside entrance_inside quadrants
  · intro p member
    exact ⟨member.1, member.2.1, member.2.2.1.trans_le first_bound_le⟩
  · intro p member
    exact ⟨member.1, member.2.1, member.2.2.1.trans_le last_bound_le⟩
  · intro p member
    exact member.2.2.2
  · intro p member
    exact member.2.2.2

end Unfoldings.ConvexCap.SectorForest
