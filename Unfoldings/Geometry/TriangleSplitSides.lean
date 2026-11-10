module

public import Unfoldings.Geometry.TriangleSplit

/-! The elementary split covers exactly the old triangle, with one shared edge and no overlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T : Triangle) (t : ℝ) (inside : t ∈ Set.Ioo 0 1)

def splitHeight : Plane →ᵃ[ℝ] ℝ := (1 - t) • T.coord 1 - t • T.coord 0

@[simp] theorem splitHeight_first : T.splitHeight t (T.vertex 0) = -t := by
  simp [splitHeight]

@[simp] theorem splitHeight_last : T.splitHeight t (T.vertex 1) = 1 - t := by
  simp [splitHeight]

@[simp] theorem splitHeight_opposite : T.splitHeight t (T.vertex 2) = 0 := by
  simp [splitHeight]

@[simp] theorem splitHeight_splitPoint : T.splitHeight t (T.splitPoint t) = 0 := by
  rw [splitPoint, (T.splitHeight t).apply_lineMap, splitHeight_first, splitHeight_last]
  simp [AffineMap.lineMap_apply_ring]
  ring

theorem splitHeight_left (x : Plane) :
    T.splitHeight t x = -t * (T.splitTriangle t inside false).coord 0 x := by
  have equal := (T.splitTriangle t inside false).affine_height_eq_coord 1 (T.splitHeight t)
    (T.splitHeight_splitPoint t) (T.splitHeight_opposite t) x
  change T.splitHeight t x = T.splitHeight t (T.vertex 0) *
    (T.splitTriangle t inside false).coord 0 x at equal
  rwa [splitHeight_first] at equal

theorem splitHeight_right (x : Plane) :
    T.splitHeight t x = (1 - t) * (T.splitTriangle t inside true).coord 1 x := by
  have equal := (T.splitTriangle t inside true).affine_height_eq_coord 2 (T.splitHeight t)
    (T.splitHeight_opposite t) (T.splitHeight_splitPoint t) x
  change T.splitHeight t x = T.splitHeight t (T.vertex 1) *
    (T.splitTriangle t inside true).coord 1 x at equal
  rwa [splitHeight_last] at equal

theorem splitTriangle_intersection {x : Plane}
    (first : x ∈ (T.splitTriangle t inside false).carrier)
    (last : x ∈ (T.splitTriangle t inside true).carrier) :
    x ∈ (T.splitTriangle t inside false).edge 1 := by
  have left_nonneg := (T.splitTriangle t inside false).carrier_eq_nonneg_coord.le first 0
  have right_nonneg := (T.splitTriangle t inside true).carrier_eq_nonneg_coord.le last 1
  have left := T.splitHeight_left t inside x
  have right := T.splitHeight_right t inside x
  have zero : T.splitHeight t x = 0 := by nlinarith [inside.1, inside.2]
  have coord : (T.splitTriangle t inside false).coord 0 x = 0 := by
    nlinarith [inside.1]
  exact ((T.splitTriangle t inside false).mem_edge_iff 1 x).mpr ⟨first, coord⟩

theorem splitTriangle_nonoverlapping :
    Disjoint (interior (T.splitTriangle t inside false).carrier)
      (interior (T.splitTriangle t inside true).carrier) := by
  apply Set.disjoint_left.mpr
  intro x first last
  have positive_left := (T.splitTriangle t inside false).interior_eq_pos_coord.le first 0
  have positive_right := (T.splitTriangle t inside true).interior_eq_pos_coord.le last 1
  have left := T.splitHeight_left t inside x
  have right := T.splitHeight_right t inside x
  nlinarith [inside.1, inside.2]

theorem splitTriangle_subset (side : Bool) :
    (T.splitTriangle t inside side).carrier ⊆ T.carrier := by
  intro x member
  rw [← T.splitTriangle_cover t inside]
  cases side
  · exact Or.inl member
  · exact Or.inr member

end Unfoldings.Triangle
