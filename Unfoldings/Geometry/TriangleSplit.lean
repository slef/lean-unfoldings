module

public import Unfoldings.Geometry.EdgeSides
public import Mathlib.Analysis.Convex.Join

/-! Split an actual triangle from an interior point of one edge to its opposite corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem segment_lineMap_split (a b : Plane) {t : ℝ} (inside : t ∈ Set.Icc 0 1) :
    segment ℝ a b = segment ℝ a (AffineMap.lineMap a b t) ∪
      segment ℝ (AffineMap.lineMap a b t) b := by
  let L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a b
  have first : L '' Set.Icc 0 t = segment ℝ a (L t) := by
    rw [← segment_eq_Icc inside.1, image_segment]
    simp [L]
  have last : L '' Set.Icc t 1 = segment ℝ (L t) b := by
    rw [← segment_eq_Icc inside.2, image_segment]
    simp [L]
  rw [segment_eq_image_lineMap, ← Set.Icc_union_Icc_eq_Icc inside.1 inside.2,
    Set.image_union, first, last]

namespace Triangle

theorem carrier_eq_three (T : Triangle) :
    T.carrier = convexHull ℝ {T.vertex 0, T.vertex 1, T.vertex 2} := by
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

def splitPoint (T : Triangle) (t : ℝ) : Plane := AffineMap.lineMap (T.vertex 0) (T.vertex 1) t

theorem orient_split_left (T : Triangle) (t : ℝ) :
    orient (T.vertex 0) (T.splitPoint t) (T.vertex 2) =
      t * orient (T.vertex 0) (T.vertex 1) (T.vertex 2) := by
  simp [splitPoint, orient, AffineMap.lineMap_apply_module']
  ring

theorem orient_split_right (T : Triangle) (t : ℝ) :
    orient (T.splitPoint t) (T.vertex 1) (T.vertex 2) =
      (1 - t) * orient (T.vertex 0) (T.vertex 1) (T.vertex 2) := by
  simp [splitPoint, orient, AffineMap.lineMap_apply_module']
  ring

def splitTriangle (T : Triangle) (t : ℝ) (inside : t ∈ Set.Ioo 0 1) (side : Bool) : Triangle where
  vertex := if side then ![T.splitPoint t, T.vertex 1, T.vertex 2]
    else ![T.vertex 0, T.splitPoint t, T.vertex 2]
  nondegenerate := by
    cases side
    · change orient (T.vertex 0) (T.splitPoint t) (T.vertex 2) ≠ 0
      rw [orient_split_left]
      exact mul_ne_zero inside.1.ne' T.nondegenerate
    · change orient (T.splitPoint t) (T.vertex 1) (T.vertex 2) ≠ 0
      rw [orient_split_right]
      exact mul_ne_zero (sub_pos.mpr inside.2).ne' T.nondegenerate

theorem splitTriangle_cover (T : Triangle) (t : ℝ) (inside : t ∈ Set.Ioo 0 1) :
    (T.splitTriangle t inside false).carrier ∪ (T.splitTriangle t inside true).carrier =
      T.carrier := by
  rw [carrier_eq_three, carrier_eq_three, carrier_eq_three]
  change convexHull ℝ {T.vertex 0, T.splitPoint t, T.vertex 2} ∪
      convexHull ℝ {T.splitPoint t, T.vertex 1, T.vertex 2} =
    convexHull ℝ {T.vertex 0, T.vertex 1, T.vertex 2}
  rw [← convexJoin_segment_singleton, ← convexJoin_segment_singleton,
    ← convexJoin_segment_singleton, ← convexJoin_union_left]
  unfold splitPoint
  rw [← segment_lineMap_split _ _ ⟨inside.1.le, inside.2.le⟩]

end Triangle
end Unfoldings
