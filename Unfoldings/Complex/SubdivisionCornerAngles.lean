module

public import Unfoldings.Complex.SubdivisionMetric
public import Unfoldings.Complex.Angles
public import Unfoldings.Geometry.Endpoints

/-! Geometric corner-angle conservation transports actual retained vertex fan angles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child} (S : C.Subdivision D)

/-- A fine corner lies at this very corner of its named original parent. -/
def RefinesCorner (fine : D.Corner) (coarse : C.Corner) : Prop :=
  S.parent fine.1 = coarse.1 ∧
    S.place fine.1 ((D.triangle fine.1).vertex fine.2) = (C.triangle coarse.1).vertex coarse.2

open Classical in
/-- Actual fine corners over each original corner carry exactly its original angle. -/
def CornerAnglePreserving : Prop := ∀ c : C.Corner,
  (∑ d : D.Corner, if S.RefinesCorner d c then (D.triangle d.1).cornerAngle d.2 else 0) =
    (C.triangle c.1).cornerAngle c.2

theorem refinesCorner_unique {d : D.Corner} {a b : C.Corner}
    (first : S.RefinesCorner d a) (last : S.RefinesCorner d b) : a = b := by
  rcases a with ⟨f, i⟩
  rcases b with ⟨g, j⟩
  have same : f = g := first.1.symm.trans last.1
  subst g
  exact Prod.ext rfl ((C.triangle f).vertex_injective (first.2.symm.trans last.2))

theorem point_parent_refined_corner (retain : Set C.Seam) {d : D.Corner} {c : C.Corner}
    (refines : S.RefinesCorner d c) :
    MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
      C.vertexPoint retain (C.vertexOfCorner retain c) := by
  have equal := S.parentPoint_eq (y := (D.cornerPoint d).2) (x := (C.cornerPoint c).2)
    refines.1 refines.2
  exact congrArg (MetricGluing.point C.Cell (C.glue retain)) equal

theorem exists_refined_corner_of_parent_vertex (retain : Set C.Seam) (d : D.Corner)
    (vertex : C.Vertex retain)
    (equal : MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
      C.vertexPoint retain vertex) :
    ∃ c : C.Corner, S.RefinesCorner d c ∧ C.vertexOfCorner retain c = vertex := by
  have old_vertex := (C.mem_range_vertexPoint_iff retain (S.parentPoint (D.cornerPoint d))).mp
    ⟨vertex, equal.symm⟩
  obtain ⟨i, at_corner⟩ := old_vertex
  let c : C.Corner := (S.parent d.1, i)
  have refines : S.RefinesCorner d c := ⟨rfl, at_corner.symm⟩
  refine ⟨c, refines, ?_⟩
  apply C.vertexPoint_injective retain
  exact (S.point_parent_refined_corner retain refines).symm.trans equal

open Classical in
theorem parent_vertex_weight_eq_corner_sum (retain : Set C.Seam) (d : D.Corner)
    (vertex : C.Vertex retain) (weight : ℝ) :
    (if MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
        C.vertexPoint retain vertex then weight else 0) =
      ∑ c : C.Corner, if C.vertexOfCorner retain c = vertex then
        (if S.RefinesCorner d c then weight else 0) else 0 := by
  classical
  by_cases equal : MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
      C.vertexPoint retain vertex
  · rw [ite_eq_left equal]
    obtain ⟨c, refines, original⟩ := S.exists_refined_corner_of_parent_vertex retain d vertex equal
    symm
    rw [Finset.sum_eq_single c]
    · simp only [original, refines, ite_true]
    · intro b _ different
      by_cases classes : C.vertexOfCorner retain b = vertex
      · by_cases matched : S.RefinesCorner d b
        · exact (different (S.refinesCorner_unique matched refines)).elim
        · simp only [classes, matched, ite_true, ite_false]
      · simp only [classes, ite_false]
    · intro absent
      exact (absent (Finset.mem_univ _)).elim
  · rw [ite_eq_right equal]
    symm
    apply Finset.sum_eq_zero
    intro c _
    by_cases classes : C.vertexOfCorner retain c = vertex
    · by_cases matched : S.RefinesCorner d c
      · exact (equal ((S.point_parent_refined_corner retain matched).trans
          (congrArg (C.vertexPoint retain) classes))).elim
      · simp only [classes, matched, ite_true, ite_false]
    · simp only [classes, ite_false]

open Classical in
/-- Geometrically grouped fine corners preserve every actual old retained vertex fan. -/
theorem sum_angles_over_parent_vertex (preserving : S.CornerAnglePreserving)
    (retain : Set C.Seam) (vertex : C.Vertex retain) :
    (∑ d : D.Corner,
      if MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
        C.vertexPoint retain vertex then (D.triangle d.1).cornerAngle d.2 else 0) =
      C.totalAngle retain vertex := by
  classical
  simp_rw [S.parent_vertex_weight_eq_corner_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ c : C.Corner, if C.vertexOfCorner retain c = vertex then
        (∑ d : D.Corner, if S.RefinesCorner d c then (D.triangle d.1).cornerAngle d.2 else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases same : C.vertexOfCorner retain c = vertex <;> simp only [same, ite_true,
        ite_false, Finset.sum_const_zero]
    _ = C.totalAngle retain vertex := by
      exact Finset.sum_congr rfl (fun c _ => by rw [preserving])

/-- Angle conservation forces a genuine fine corner over every old corner. -/
theorem exists_refinedCorner (preserving : S.CornerAnglePreserving) (c : C.Corner) :
    ∃ d : D.Corner, S.RefinesCorner d c := by
  classical
  by_contra absent
  have zero : (∑ d : D.Corner,
      if S.RefinesCorner d c then (D.triangle d.1).cornerAngle d.2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    exact ite_eq_right (fun matched => absent ⟨d, matched⟩)
  exact (ne_of_gt ((C.triangle c.1).cornerAngle_pos c.2)) ((preserving c).symm.trans zero)

namespace Conforming

variable {S} {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (H : S.Conforming retain fineRetain)

open Classical in
/-- Grouping actual fine vertex fans by the conforming metric equivalence preserves old fans. -/
theorem sum_totalAngle_over_vertex (preserving : S.CornerAnglePreserving)
    (vertex : C.Vertex retain) :
    (∑ w : D.Vertex fineRetain,
      if H.metricEquiv (D.vertexPoint fineRetain w) = C.vertexPoint retain vertex
      then D.totalAngle fineRetain w else 0) = C.totalAngle retain vertex := by
  classical
  calc
    _ = ∑ d : D.Corner,
        if MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
          C.vertexPoint retain vertex then (D.triangle d.1).cornerAngle d.2 else 0 := by
      have image (d : D.Corner) : H.metricEquiv
          (MetricGluing.point D.Cell (D.glue fineRetain) (D.cornerPoint d)) =
            MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) :=
        H.metricEquiv_faceMap d.1 (D.cornerPoint d).2
      simpa only [TriangleComplex.totalAngle, Finset.sum_filter, Finset.mem_filter,
        Finset.mem_univ, true_and, TriangleComplex.vertexPoint_vertexOfCorner, image] using
        Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset D.Corner)
          (Finset.univ.filter fun w =>
            H.metricEquiv (D.vertexPoint fineRetain w) = C.vertexPoint retain vertex)
          (D.vertexOfCorner fineRetain) (fun d => (D.triangle d.1).cornerAngle d.2)
    _ = _ := S.sum_angles_over_parent_vertex preserving retain vertex

/-- The unique fine copy above an old metric vertex has exactly its retained fan angle. -/
theorem totalAngle_eq_of_vertexPoint (preserving : S.CornerAnglePreserving)
    (fine : D.Vertex fineRetain) (coarse : C.Vertex retain)
    (same : H.metricEquiv (D.vertexPoint fineRetain fine) = C.vertexPoint retain coarse) :
    D.totalAngle fineRetain fine = C.totalAngle retain coarse := by
  classical
  rw [← H.sum_totalAngle_over_vertex preserving coarse, Finset.sum_eq_single fine]
  · simp only [same, ite_true]
  · intro w _ different
    apply ite_eq_right
    intro equal
    apply different
    exact D.vertexPoint_injective fineRetain (H.metricEquiv.injective (equal.trans same.symm))
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

/-- Every old retained vertex has a unique actual fine vertex copy above it. -/
theorem existsUnique_vertex_over (preserving : S.CornerAnglePreserving)
    (coarse : C.Vertex retain) : ∃! fine : D.Vertex fineRetain,
      H.metricEquiv (D.vertexPoint fineRetain fine) = C.vertexPoint retain coarse := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain coarse
  obtain ⟨d, matched⟩ := S.exists_refinedCorner preserving c
  refine ⟨D.vertexOfCorner fineRetain d, S.point_parent_refined_corner retain matched, ?_⟩
  intro w equal
  apply D.vertexPoint_injective fineRetain
  apply H.metricEquiv.injective
  exact equal.trans (S.point_parent_refined_corner retain matched).symm

end Conforming

end Unfoldings.TriangleComplex.Subdivision
