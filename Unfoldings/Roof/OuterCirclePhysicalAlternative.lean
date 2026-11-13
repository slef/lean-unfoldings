module

public import Unfoldings.Roof.OuterCircleContactAlternative
public import Unfoldings.Roof.BoundaryCirclePhysicalAlternative

/-! Outer-bank circle endpoints have a common physical point or one actual radial component. -/

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

theorem outer_circle_physical_endpoints_eq_or_common_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (leaf_coherent : ∀ i, ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i j : FiveSector}
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : R.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : R.RadialStripTraceData positive small D calibration j T ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (shared : fiveSectorFirst t i = fiveSectorLast t j)
    (first_outer : Set.EqOn S.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain)) :
    ((fiveSectorFrame t positive small i).place.symm (S.upper.point slice.upperHeight) =
        (fiveSectorFrame t positive small j).place.symm (T.lower.point other_slice.lowerHeight) ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight))) ∨
      ∃ c : F.Component,
        origin + (fiveSectorFrame t positive small i).place.symm
          (S.upper.point slice.upperHeight) ∈ (F.componentTail c).carrier ∧
        origin + (fiveSectorFrame t positive small j).place.symm
          (T.lower.point other_slice.lowerHeight) ∈ (F.componentTail c).carrier ∧
        ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
          M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  have first_height := (data.circle_slice_heights radius_positive far slice).2
  have last_height := (other.circle_slice_heights radius_positive far other_slice).1
  rcases shared_sector_bank_point_order positive small shared first_height.1 last_height.1 with
    ⟨a, bounds, contact⟩ | ⟨b, bounds, contact⟩
  · have a_bounds : a ∈ Set.Icc 0 cutoff := ⟨bounds.1.le, bounds.2.trans last_height.2.le⟩
    have actual_contact : (fiveSectorFrame t positive small i).place.symm
        (S.upper.point slice.upperHeight) =
        (fiveSectorFrame t positive small j).place.symm (T.lower.point a) := by
      rw [first_outer ⟨first_height.1.le, first_height.2.le⟩, last_outer a_bounds]
      exact contact
    exact M.boundary_circle_physical_contact_or_common_component F covered positive small R D
      leaf_coherent data other T.lower (Or.inl rfl) false slice.upper_closed
      other_slice.lower_closed
      bounds.1 bounds.2 last_height.2 radius_positive slice.upper_radius other_slice.lower_radius
      deep actual_contact (last_outer a_bounds) (last_outer ⟨last_height.1.le, last_height.2.le⟩)
  · have b_bounds : b ∈ Set.Icc 0 cutoff := ⟨bounds.1.le, bounds.2.trans first_height.2.le⟩
    have actual_contact : (fiveSectorFrame t positive small j).place.symm
        (T.lower.point other_slice.lowerHeight) =
        (fiveSectorFrame t positive small i).place.symm (S.upper.point b) := by
      rw [last_outer ⟨last_height.1.le, last_height.2.le⟩, first_outer b_bounds]
      exact contact
    rcases M.boundary_circle_physical_contact_or_common_component F covered positive small R D
      leaf_coherent other data S.upper (Or.inr rfl) true other_slice.lower_closed
      slice.upper_closed
      bounds.1 bounds.2 first_height.2 radius_positive other_slice.lower_radius slice.upper_radius
      deep actual_contact (first_outer b_bounds)
      (first_outer ⟨first_height.1.le, first_height.2.le⟩) with
      common | ⟨c, first, last, unattached⟩
    · exact Or.inl ⟨common.1.symm, common.2.symm⟩
    · exact Or.inr ⟨c, last, first, unattached⟩

end Unfoldings.ConvexRoof.SectorForest
