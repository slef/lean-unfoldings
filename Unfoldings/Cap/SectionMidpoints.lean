module

public import Unfoldings.Cap.SectionTrace
public import Unfoldings.Geometry.LineCrossingSides

/-!
# Actual interior sample points of regular section pieces

The middle of each positive-length original-face section piece lies in that
face's interior. A zero barycentric coordinate would put the whole section line
on an original edge, contradicting original-vertex avoidance.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectionFaceTrace

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)

def middleTime (i : Fin (T.turns + 1)) : ℝ :=
  ((T.time i.castSucc : ℝ) + (T.time i.succ : ℝ)) / 2

def middlePoint (i : Fin (T.turns + 1)) : Plane :=
  AffineMap.lineMap (T.point i.castSucc) (T.point i.succ) (1 / 2 : ℝ)

theorem middlePoint_eq_section (i : Fin (T.turns + 1)) :
    T.middlePoint i = AffineMap.lineMap p q (T.middleTime i) := by
  ext j
  simp only [middlePoint, middleTime, point, AffineMap.lineMap_apply_module',
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-- Regular sections have genuine interior sample points in every actual labeled original face. -/
theorem middlePoint_interior (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin (T.turns + 1)) :
    T.middlePoint i ∈ interior (K.projectedTriangle (T.face i)).carrier := by
  let triangle := K.projectedTriangle (T.face i)
  rw [Triangle.interior_eq_pos_coord]
  intro j
  have first_nonneg := triangle.carrier_eq_nonneg_coord.le (T.point_mem_face_first i) j
  have last_nonneg := triangle.carrier_eq_nonneg_coord.le (T.point_mem_face_last i) j
  have middle : triangle.coord j (T.middlePoint i) =
      (triangle.coord j (T.point i.castSucc) + triangle.coord j (T.point i.succ)) / 2 := by
    rw [middlePoint, (triangle.coord j).apply_lineMap, AffineMap.lineMap_apply_ring]
    ring
  by_contra nonpositive
  have first_zero : triangle.coord j (T.point i.castSucc) = 0 := by
    rw [middle] at nonpositive
    linarith
  have last_zero : triangle.coord j (T.point i.succ) = 0 := by
    rw [middle] at nonpositive
    linarith
  have first_area : orient (triangle.vertex (Triangle.next j))
      (triangle.vertex (Triangle.next (Triangle.next j))) (T.point i.castSucc) = 0 := by
    rw [triangle.orient_eq_coord_mul (Triangle.next j), Triangle.next_next_next,
      first_zero, mul_zero]
  have last_area : orient (triangle.vertex (Triangle.next j))
      (triangle.vertex (Triangle.next (Triangle.next j))) (T.point i.succ) = 0 := by
    rw [triangle.orient_eq_coord_mul (Triangle.next j), Triangle.next_next_next,
      last_zero, mul_zero]
  have transverse := line_transverse_of_avoids_endpoint
    (triangle.edge_endpoints_ne (Triangle.next j)) different
    (fun t => regular t (T.face i) (Triangle.next j)) (T.time i.castSucc : ℝ) first_area
  have identity := orient_lineMap_sub (triangle.vertex (Triangle.next j))
    (triangle.vertex (Triangle.next (Triangle.next j))) p q
    (T.time i.succ : ℝ) (T.time i.castSucc : ℝ)
  simp only [point] at last_area first_area
  rw [last_area, first_area, sub_self] at identity
  exact (mul_ne_zero (ne_of_gt (T.time_step_pos i)) transverse) identity.symm

end Unfoldings.ConvexCap.SectionFaceTrace
