module

public import Unfoldings.Cap.SectionMidpoints
public import Unfoldings.Cap.SectionTransitions
public import Unfoldings.Cap.ProjectedOpening

/-!
# Whole open section pieces avoid all original seams

Vertex avoidance makes the middle point interior. Positive barycentric
coordinates then put the whole open piece in the same original face interior.
No original seam can meet any original face interior, by injective projection
and the distinctness of its two actual incident faces.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Every original seam avoids every original projected face interior. -/
theorem projected_seam_not_mem_face_interior (s : C.Seam) (f : Face) {z : Plane}
    (inside : z ∈ interior (K.projectedTriangle f).carrier) :
    z ∉ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
  intro member
  have left := K.projected_face_unique_of_interior inside
    ((K.projectedTriangle (C.left s).face).edge_subset _ member)
  have right_member := K.projected_seam_edges_eq s ▸ member
  have right := K.projected_face_unique_of_interior inside
    ((K.projectedTriangle (C.right s).face).edge_subset _ right_member)
  exact K.folding.incident_faces_ne s (left.trans right.symm)

namespace SectionFaceTrace

variable {K} {p q : Plane} (T : K.SectionFaceTrace p q)

/-- The entire open original-face section piece is interior, not only its middle point. -/
theorem piece_interior (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin (T.turns + 1)) {r : ℝ} (positive : 0 < r) (small : r < 1) :
    AffineMap.lineMap (T.point i.castSucc) (T.point i.succ) r ∈
      interior (K.projectedTriangle (T.face i)).carrier := by
  let triangle := K.projectedTriangle (T.face i)
  have middle_inside := T.middlePoint_interior different regular i
  rw [Triangle.interior_eq_pos_coord] at middle_inside ⊢
  intro j
  have first_nonneg := triangle.carrier_eq_nonneg_coord.le (T.point_mem_face_first i) j
  have last_nonneg := triangle.carrier_eq_nonneg_coord.le (T.point_mem_face_last i) j
  have middle := middle_inside j
  have middle_eq : triangle.coord j (T.middlePoint i) =
      (triangle.coord j (T.point i.castSucc) + triangle.coord j (T.point i.succ)) / 2 := by
    rw [middlePoint, (triangle.coord j).apply_lineMap, AffineMap.lineMap_apply_ring]
    ring
  have endpoint : 0 < triangle.coord j (T.point i.castSucc) ∨
      0 < triangle.coord j (T.point i.succ) := by
    rw [middle_eq] at middle
    by_contra neither
    push Not at neither
    linarith
  rw [(triangle.coord j).apply_lineMap, AffineMap.lineMap_apply_ring]
  rcases endpoint with first | last
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr small) first)
      (mul_nonneg positive.le last_nonneg)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr small.le) first_nonneg)
      (mul_pos positive last)

/-- Every real section parameter strictly within an actual face interval is interior. -/
theorem point_interior_of_time_between (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin (T.turns + 1)) {r : ℝ}
    (lower : (T.time i.castSucc : ℝ) < r) (upper : r < (T.time i.succ : ℝ)) :
    AffineMap.lineMap p q r ∈ interior (K.projectedTriangle (T.face i)).carrier := by
  let a := (T.time i.castSucc : ℝ)
  let b := (T.time i.succ : ℝ)
  have step : 0 < b - a := T.time_step_pos i
  have positive : 0 < (r - a) / (b - a) := div_pos (sub_pos.mpr lower) step
  have small : (r - a) / (b - a) < 1 := (div_lt_one step).mpr (by linarith)
  have image : AffineMap.lineMap (T.point i.castSucc) (T.point i.succ) ((r - a) / (b - a)) =
      AffineMap.lineMap p q r := by
    rw [AffineMap.lineMap_apply_module', T.point_sub, smul_smul]
    change ((r - a) / (b - a) * (b - a)) • (q - p) + T.point i.castSucc = _
    rw [div_mul_cancel₀ _ (ne_of_gt step)]
    simp only [point, AffineMap.lineMap_apply_module']
    change (r - a) • (q - p) + (a • (q - p) + p) = r • (q - p) + p
    module
  rw [← image]
  exact T.piece_interior different regular i positive small

/-- No original seam enters the actual open portion of any regular original-face piece. -/
theorem seam_avoids_open_piece (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin (T.turns + 1)) {r : ℝ} (positive : 0 < r) (small : r < 1) (s : C.Seam) :
    AffineMap.lineMap (T.point i.castSucc) (T.point i.succ) r ∉
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge :=
  K.projected_seam_not_mem_face_interior s (T.face i)
    (T.piece_interior different regular i positive small)

end SectionFaceTrace
end Unfoldings.ConvexCap
