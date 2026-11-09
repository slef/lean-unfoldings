module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Polygon edges with boundary contact allowed

Different edges may share endpoints, but an open edge meets no other closed
edge. This permits collinear subdivisions, unlike affine independence of
every three consecutive vertices. The definitions are independent of
polyhedra and do not assume any angle-sum conclusion.
-/

@[expose] public section

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def HasDisjointOpenEdges (poly : Polygon E n) : Prop :=
  ∀ i j, i ≠ j → Disjoint (openSegment ℝ (poly i) (poly (finRotate n i)))
    (segment ℝ (poly j) (poly (finRotate n j)))

theorem HasDisjointOpenEdges.three_le [NeZero n] {poly : Polygon E n}
    (disjoint : poly.HasDisjointOpenEdges) (nondegenerate : poly.HasNondegenerateEdges) :
    3 ≤ n := by
  have at_least_two := nondegenerate.two_le
  by_contra small
  have two : n = 2 := by omega
  subst n
  have apart := disjoint 0 1 (by intro equal; have := congrArg Fin.val equal; norm_num at this)
  have rotate_zero : finRotate 2 0 = 1 := finRotate_apply_zero
  have rotate_one : finRotate 2 1 = 0 := finRotate_last
  rw [rotate_zero, rotate_one, segment_symm ℝ (poly 1) (poly 0)] at apart
  exact Set.disjoint_left.mp apart (midpoint_mem_openSegment (poly 0) (poly 1))
    (midpoint_mem_segment (poly 0) (poly 1))

end Polygon
