module

public import Unfoldings.Cone.ConsecutiveSectors
public import Unfoldings.Cone.ReentrantSectorTopology
public import Unfoldings.Metric.GroupedPolygonalCover

/-! Consecutive intrinsic sectors retain the summed metric through their actual common bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Keep both original pieces whole, allowing either original sector to be reentrant. -/
def consecutiveSectorRegion (a b : ℝ) : Bool → Set ℂ
  | false => closedAngularSector a
  | true => rotation (Circle.exp a) '' closedAngularSector b

abbrev ConsecutiveSectorGluing (a b : ℝ) :=
  MetricGluing.Realization (fun i => PolygonalPoint (consecutiveSectorRegion a b i))
    (MetricGluing.polygonalCoincident (consecutiveSectorRegion a b))

/-- The entire joined intrinsic metric is exactly the summed geometric sector metric.
The finite convex cover is constructed from the two original sectors, rather than supplied. -/
def consecutiveSectorIsometryEquiv (a b : ℝ) (first : 0 < a) (last : 0 < b)
    (small : a + b < 2 * Real.pi) :
    ConsecutiveSectorGluing a b ≃ᵢ PolygonalPoint (closedAngularSector (a + b)) := by
  let A := bisectedSectorFan a first (by linarith)
  let B := bisectedSectorFan b last (by linarith)
  let R := rotation (Circle.exp a)
  have first_cover : (⋃ i, A.faceImage i) = closedAngularSector a := by
    have same := A.planarRegion_eq_closedAngularSector
    rw [bisectedSectorFan_totalAngle] at same
    exact same
  have last_cover : (⋃ i, B.faceImage i) = closedAngularSector b := by
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
  have contained (j : Fin 2 ⊕ Fin 2) : cells j ⊆ consecutiveSectorRegion a b (owner j) := by
    cases j with
    | inl i =>
      change A.faceImage i ⊆ closedAngularSector a
      rw [← first_cover]
      exact Set.subset_iUnion _ i
    | inr i =>
      change R '' B.faceImage i ⊆ R '' closedAngularSector b
      apply Set.image_mono
      rw [← last_cover]
      exact Set.subset_iUnion _ i
  have cover : closedAngularSector (a + b) = ⋃ j, cells j := by
    rw [Set.iUnion_sum]
    change closedAngularSector (a + b) = (⋃ i, A.faceImage i) ∪ (⋃ i, R '' B.faceImage i)
    rw [← Set.image_iUnion, first_cover, last_cover]
    exact (closedAngularSector_union_consecutive a b first.le last.le).symm
  have inside (i : Bool) : consecutiveSectorRegion a b i ⊆ closedAngularSector (a + b) := by
    rw [← closedAngularSector_union_consecutive a b first.le last.le]
    cases i
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  exact MetricGluing.groupedCoverIsometryEquiv (consecutiveSectorRegion a b) inside
    cells owner contained cover closed convex

@[simp] theorem consecutiveSectorIsometryEquiv_point (a b : ℝ) (first : 0 < a)
    (last : 0 < b) (small : a + b < 2 * Real.pi)
    (x : MetricGluing.Total (fun i => PolygonalPoint (consecutiveSectorRegion a b i))) :
    (consecutiveSectorIsometryEquiv a b first last small
      (MetricGluing.point _
        (MetricGluing.polygonalCoincident (consecutiveSectorRegion a b)) x)).val =
        x.2.val := rfl

/-- An inserted zero-angle bank adds no distance shortcuts or extra points to the sector. -/
def consecutiveSectorZeroIsometryEquiv (a : ℝ) (positive : 0 < a) (small : a < 2 * Real.pi) :
    ConsecutiveSectorGluing a 0 ≃ᵢ PolygonalPoint (closedAngularSector a) := by
  let A := bisectedSectorFan a positive small
  have cover : closedAngularSector a = ⋃ i, A.faceImage i := by
    have same := A.planarRegion_eq_closedAngularSector
    rw [bisectedSectorFan_totalAngle] at same
    exact same.symm
  have union_eq : closedAngularSector a ∪ rotation (Circle.exp a) '' closedAngularSector 0 =
      closedAngularSector a := by
    simpa only [add_zero] using closedAngularSector_union_consecutive a 0 positive.le le_rfl
  have inside (i : Bool) : consecutiveSectorRegion a 0 i ⊆ closedAngularSector a := by
    cases i
    · exact Set.Subset.refl _
    · intro z member
      exact union_eq ▸ (Or.inr member)
  have contained (j : Fin 2) : A.faceImage j ⊆ consecutiveSectorRegion a 0 false := by
    change A.faceImage j ⊆ closedAngularSector a
    rw [cover]
    exact Set.subset_iUnion _ j
  exact MetricGluing.groupedCoverIsometryEquiv (consecutiveSectorRegion a 0) inside
    A.faceImage (fun _ => false) contained cover A.isClosed_faceImage A.convex_faceImage

@[simp] theorem consecutiveSectorZeroIsometryEquiv_point (a : ℝ) (positive : 0 < a)
    (small : a < 2 * Real.pi)
    (x : MetricGluing.Total (fun i => PolygonalPoint (consecutiveSectorRegion a 0 i))) :
    (consecutiveSectorZeroIsometryEquiv a positive small
      (MetricGluing.point _
        (MetricGluing.polygonalCoincident (consecutiveSectorRegion a 0)) x)).val =
        x.2.val := rfl

/-- The joined metric also handles a flat insertion with zero angle. -/
def consecutiveSectorNonnegIsometryEquiv (a b : ℝ) (first : 0 < a) (last : 0 ≤ b)
    (small : a + b < 2 * Real.pi) :
    ConsecutiveSectorGluing a b ≃ᵢ PolygonalPoint (closedAngularSector (a + b)) := by
  by_cases positive : 0 < b
  · exact consecutiveSectorIsometryEquiv a b first positive small
  · have zero : b = 0 := le_antisymm (le_of_not_gt positive) last
    subst b
    exact (consecutiveSectorZeroIsometryEquiv a first (by simpa only [add_zero] using small)).trans
      (PolygonalPoint.congrIsometryEquiv (congrArg closedAngularSector (add_zero a).symm))

@[simp] theorem consecutiveSectorNonnegIsometryEquiv_point (a b : ℝ) (first : 0 < a)
    (last : 0 ≤ b) (small : a + b < 2 * Real.pi)
    (x : MetricGluing.Total (fun i => PolygonalPoint (consecutiveSectorRegion a b i))) :
    (consecutiveSectorNonnegIsometryEquiv a b first last small
      (MetricGluing.point _
        (MetricGluing.polygonalCoincident (consecutiveSectorRegion a b)) x)).val =
        x.2.val := by
  by_cases positive : 0 < b
  · simp only [consecutiveSectorNonnegIsometryEquiv, dite_eq_left positive,
      consecutiveSectorIsometryEquiv_point]
  · have zero : b = 0 := le_antisymm (le_of_not_gt positive) last
    subst b
    simp only [consecutiveSectorNonnegIsometryEquiv, dite_eq_right (lt_irrefl (0 : ℝ)),
      IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
      consecutiveSectorZeroIsometryEquiv_point]

end Unfoldings
