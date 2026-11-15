module

public import Unfoldings.Cone.ComplementarySectors
public import Unfoldings.Metric.GroupedPolygonalCover

/-! Two complementary intrinsic geometric sectors, glued only at their bank points, form a plane. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalPoint

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unrestricted intrinsic polygonal metric is exactly the ambient normed-space metric. -/
def univIsometryEquiv : PolygonalPoint (Set.univ : Set E) ≃ᵢ E where
  toFun := PolygonalPoint.val
  invFun z := ⟨z, Set.mem_univ z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun x y :=
    (edist_eq_of_segment (x := x) (y := y) (fun z _ => Set.mem_univ z)).symm

end Unfoldings.PolygonalPoint

namespace Unfoldings

/-- Each piece retains its own intrinsic metric, allowing a reentrant piece on either side. -/
def complementarySectorRegion (width : ℝ) : Bool → Set ℂ
  | false => closedAngularSector width
  | true => complementarySector width

abbrev ComplementarySectorCompletion (width : ℝ) :=
  MetricGluing.Realization (fun b => PolygonalPoint (complementarySectorRegion width b))
    (MetricGluing.polygonalCoincident (complementarySectorRegion width))

/-- The actual two-piece sector metric is the plane metric, for every genuine corner angle.
The convex halves are used only to prove the metric comparison, not as input certificates. -/
def complementarySectorPlaneIsometryEquiv (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi) : ComplementarySectorCompletion width ≃ᵢ ℂ := by
  let A := bisectedSectorFan width positive small
  let B := bisectedSectorFan (2 * Real.pi - width) (sub_pos.mpr small) (by linarith)
  let R := rotation (Circle.exp width)
  have first_cover : (⋃ i, A.faceImage i) = closedAngularSector width := by
    have same := A.planarRegion_eq_closedAngularSector
    rw [bisectedSectorFan_totalAngle] at same
    exact same
  have last_cover : (⋃ i, B.faceImage i) = closedAngularSector (2 * Real.pi - width) := by
    have same := B.planarRegion_eq_closedAngularSector
    rw [bisectedSectorFan_totalAngle] at same
    exact same
  let cells : Fin 2 ⊕ Fin 2 → Set ℂ := Sum.elim A.faceImage (fun i => R '' B.faceImage i)
  let owner : Fin 2 ⊕ Fin 2 → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have closed (j : Fin 2 ⊕ Fin 2) : IsClosed (cells j) := by
    cases j with
    | inl i => exact A.isClosed_faceImage i
    | inr i => exact R.toHomeomorph.isClosedMap _ (B.isClosed_faceImage i)
  have convex (j : Fin 2 ⊕ Fin 2) : Convex ℝ (cells j) := by
    cases j with
    | inl i => exact A.convex_faceImage i
    | inr i => exact (B.convex_faceImage i).linear_image R.toLinearMap
  have contained (j : Fin 2 ⊕ Fin 2) : cells j ⊆ complementarySectorRegion width (owner j) := by
    cases j with
    | inl i =>
      change A.faceImage i ⊆ closedAngularSector width
      rw [← first_cover]
      exact Set.subset_iUnion _ i
    | inr i =>
      change R '' B.faceImage i ⊆ R '' closedAngularSector (2 * Real.pi - width)
      apply Set.image_mono
      rw [← last_cover]
      exact Set.subset_iUnion _ i
  have cover : (Set.univ : Set ℂ) = ⋃ j, cells j := by
    rw [Set.iUnion_sum]
    change Set.univ = (⋃ i, A.faceImage i) ∪ (⋃ i, R '' B.faceImage i)
    rw [← Set.image_iUnion, first_cover, last_cover]
    exact (closedAngularSector_union_complementary width).symm
  exact (MetricGluing.groupedCoverIsometryEquiv (complementarySectorRegion width)
    (fun _ => Set.subset_univ _) cells owner contained cover closed convex).trans
      (PolygonalPoint.univIsometryEquiv ℂ)

@[simp] theorem complementarySectorPlaneIsometryEquiv_point (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi)
    (a : MetricGluing.Total (fun b => PolygonalPoint (complementarySectorRegion width b))) :
    complementarySectorPlaneIsometryEquiv width positive small
      (MetricGluing.point _
        (MetricGluing.polygonalCoincident (complementarySectorRegion width)) a) =
        a.2.val := rfl

/-- The only cross-piece identifications are the two intended banks, at equal physical radii. -/
theorem complementarySectorCompletion_cross_banks (width : ℝ) (positive : 0 < width)
    (small : width < 2 * Real.pi)
    (x : PolygonalPoint (closedAngularSector width))
    (y : PolygonalPoint (complementarySector width)) :
    MetricGluing.point (fun b => PolygonalPoint (complementarySectorRegion width b))
      (MetricGluing.polygonalCoincident (complementarySectorRegion width)) ⟨false, x⟩ =
    MetricGluing.point (fun b => PolygonalPoint (complementarySectorRegion width b))
      (MetricGluing.polygonalCoincident (complementarySectorRegion width)) ⟨true, y⟩ ↔
      ∃ r : ℝ≥0, (x.val = (r : ℂ) ∧ y.val = (r : ℂ)) ∨
        (x.val = (r : ℂ) * polarRay width ∧ y.val = (r : ℂ) * polarRay width) := by
  constructor
  · intro equal
    have physical : x.val = y.val := congrArg
      (complementarySectorPlaneIsometryEquiv width positive small) equal
    have both : x.val ∈ closedAngularSector width ∩ complementarySector width :=
      ⟨x.property, physical ▸ y.property⟩
    rw [closedAngularSector_inter_complementary width positive small] at both
    rcases both with ⟨r, first⟩ | ⟨r, last⟩
    · exact ⟨r, Or.inl ⟨first.symm, physical.symm.trans first.symm⟩⟩
    · exact ⟨r, Or.inr ⟨last.symm, physical.symm.trans last.symm⟩⟩
  · rintro ⟨r, pair⟩
    apply MetricGluing.point_eq_of_glue
    exact pair.elim (fun h => h.1.trans h.2.symm) (fun h => h.1.trans h.2.symm)

end Unfoldings
