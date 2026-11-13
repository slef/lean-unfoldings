module

public import Unfoldings.Roof.ContactSeparatorPrefix
public import Unfoldings.Cap.ContactTraceValues
public import Unfoldings.Geometry.SubdivisionBankContact
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Actual developed traces agree on a separator's approached coherent prefix. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small i)

/-- Positive width may be witnessed at different later heights on the two
sides. Neither trace is required to meet a specified source circle. -/
theorem shared_separator_prefix_value_of_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
    {cutoff ε : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ w : M.GeometricSectorLeaf F covered positive small i,
      w.point.re + w.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G)
    (traces : ∀ S ∈ P.cells, Nonempty
      (R.RadialStripTraceData positive small D calibration i S ε cutoff))
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {S T : MonotoneStrip} (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells)
    (first_wall : S.upper = H) (last_wall : Set.EqOn H.point T.lower.point (Set.Icc 0 cutoff))
    (data : R.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : R.RadialStripTraceData positive small D calibration i T ε cutoff)
    {h a b : ℝ} (height : h ∈ Set.Icc 0 (leaf.point.re + leaf.point.im))
    (first_later : a ∈ Set.Icc h cutoff)
    (first_width : S.lower.coordinate a < S.upper.coordinate a)
    (last_later : b ∈ Set.Icc h cutoff)
    (last_width : T.lower.coordinate b < T.upper.coordinate b)
    (first_closed : S.upper.point h ∈ closure data.strictDomain)
    (last_closed : T.lower.point h ∈ closure other.strictDomain) :
    data.value (S.upper.point h) = other.value (T.lower.point h) := by
  have slab : h ∈ Set.Icc 0 cutoff := ⟨height.1, height.2.trans active⟩
  have contact : S.upper.point h = T.lower.point h := by
    rw [first_wall]
    exact last_wall slab
  have coherent : D.ProjectedCoherentAt Q
      (origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point h)) := by
    by_cases first_positive : S.lower.coordinate h < S.upper.coordinate h
    · by_cases last_positive : T.lower.coordinate h < T.upper.coordinate h
      · have inside := P.bank_contact_mem_strictCarrier first_cell last_cell contact
          first_positive last_positive
        rw [first_wall] at inside ⊢
        exact leaf.separator_prefix_coherent R D calibration deep P represented traces separator
          active completion leaf_coherent height inside
      · have collapsed : T.lower.coordinate h = T.upper.coordinate h :=
          le_antisymm (T.ordered h) (le_of_not_gt last_positive)
        have member := other.pinches h slab collapsed b last_later last_width
        have coherent := (other.physical _ (Or.inr member)
          (by rw [T.lower.point_height]; exact slab)).2
        rw [← contact] at coherent
        exact coherent
    · have collapsed : S.lower.coordinate h = S.upper.coordinate h :=
        le_antisymm (S.ordered h) (le_of_not_gt first_positive)
      have member := data.pinches h slab collapsed a first_later first_width
      have coherent := (data.physical _ (Or.inr member)
        (by rw [S.lower.point_height]; exact slab)).2
      rw [S.lower.point_eq_of_same_coordinate S.upper collapsed] at coherent
      exact coherent
  exact data.value_eq_of_coherent_contact other contact first_closed last_closed coherent

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
