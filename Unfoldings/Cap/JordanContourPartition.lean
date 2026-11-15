module

public import Unfoldings.Cap.JordanContourSegments
public import Unfoldings.Topology.ClosedPartition
public import Mathlib.Analysis.Convex.PathConnected

/-! Closed geometric arcs assign whole actual contour banks between their marked contacts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- A bank cannot pass from one closed arc to another through an actual contour vertex.
Thus whole physical banks, rather than supplied traversal labels, determine the partition. -/
theorem jordanContour_segment_subset_left_or_right {left right : Set Plane}
    (left_closed : IsClosed left) (right_closed : IsClosed right) (cover : J ⊆ left ∪ right)
    (contacts : left ∩ right ⊆ Set.range (K.jordanBankPosition jordan contains avoids))
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    segment ℝ (K.jordanBankPosition jordan contains avoids i)
        (K.jordanBankPosition jordan contains avoids
          (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) ⊆ left ∨
      segment ℝ (K.jordanBankPosition jordan contains avoids i)
        (K.jordanBankPosition jordan contains avoids
          (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) ⊆ right := by
  let a := K.jordanBankPosition jordan contains avoids i
  let b := K.jordanBankPosition jordan contains avoids
    (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)
  have on_curve : segment ℝ a b ⊆ J := by
    rw [K.jordanCurve_eq_contour_segments jordan contains avoids]
    exact Set.subset_iUnion_of_subset i Set.Subset.rfl
  have separate : Disjoint (openSegment ℝ a b) (left ∩ right) := by
    apply Set.disjoint_left.mpr
    intro p on_edge both
    obtain ⟨j, same⟩ := contacts both
    rw [← same] at on_edge
    exact K.jordanBankPosition_not_mem_open_contour_segment jordan contains avoids i j on_edge
  have split := subset_left_or_right_of_closed_cover
    (convex_openSegment (𝕜 := ℝ) a b).isPreconnected left_closed right_closed
    ((openSegment_subset_segment ℝ a b).trans (on_curve.trans cover)) separate
  rcases split with left | right
  · exact Or.inl (segment_subset_closure_openSegment.trans (closure_minimal left left_closed))
  · exact Or.inr (segment_subset_closure_openSegment.trans (closure_minimal right right_closed))

include jordan contains avoids in
open Classical in
/-- A finite geometric arc cover assigns every actual bank to one whole arc. -/
theorem jordanContour_segment_subset_piece {A : Type*} [Finite A] (piece : A → Set Plane)
    (closed : ∀ j, IsClosed (piece j)) (cover : J ⊆ ⋃ j, piece j)
    (contacts : ∀ j k, j ≠ k → piece j ∩ piece k ⊆
      Set.range (K.jordanBankPosition jordan contains avoids))
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    ∃ j, segment ℝ (K.jordanBankPosition jordan contains avoids i)
        (K.jordanBankPosition jordan contains avoids
          (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) ⊆ piece j := by
  let a := K.jordanBankPosition jordan contains avoids i
  let b := K.jordanBankPosition jordan contains avoids
    (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)
  let z := AffineMap.lineMap a b (1 / 2 : ℝ)
  have interior_point : z ∈ openSegment ℝ a b :=
    lineMap_mem_openSegment ℝ a b ⟨by norm_num, by norm_num⟩
  have on_curve : z ∈ J := by
    rw [K.jordanCurve_eq_contour_segments jordan contains avoids]
    exact Set.mem_iUnion.mpr ⟨i, openSegment_subset_segment ℝ a b interior_point⟩
  obtain ⟨j, on_piece⟩ := Set.mem_iUnion.mp (cover on_curve)
  let rest := ⋃ k : {k : A // k ≠ j}, piece k.val
  have rest_closed : IsClosed rest := isClosed_iUnion_of_finite (fun k => closed k.val)
  have actual_cover : J ⊆ piece j ∪ rest := by
    intro x hx
    obtain ⟨k, on_k⟩ := Set.mem_iUnion.mp (cover hx)
    by_cases same : k = j
    · exact Or.inl (same ▸ on_k)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, same⟩, on_k⟩)
  have common : piece j ∩ rest ⊆ Set.range (K.jordanBankPosition jordan contains avoids) := by
    rintro x ⟨first, later⟩
    obtain ⟨k, member⟩ := Set.mem_iUnion.mp later
    exact contacts j k.val k.property.symm ⟨first, member⟩
  have split := K.jordanContour_segment_subset_left_or_right jordan contains avoids
    (closed j) rest_closed actual_cover common i
  rcases split with first | later
  · exact ⟨j, first⟩
  · have both := common ⟨on_piece, later (openSegment_subset_segment ℝ a b interior_point)⟩
    obtain ⟨k, same⟩ := both
    rw [← same] at interior_point
    exact (K.jordanBankPosition_not_mem_open_contour_segment jordan contains avoids
      i k interior_point).elim

end Unfoldings.ConvexCap
