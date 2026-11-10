module

public import Unfoldings.Geometry.CornerSpan
public import Unfoldings.Geometry.Angles

/-!
# Local progress through an acute triangle

If an acute corner contains a point strictly ahead in both planar coordinates,
one of its two actual incident edges also points strictly ahead in both.
The conclusion concerns input triangle edges, not an arbitrary new diagonal.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

def StrictQuadrant (v : Plane) : Prop := 0 < v 0 ∧ 0 < v 1

/-- An acute pair cannot straddle a whole quadrant while positively spanning its interior. -/
theorem acute_generators_meet_quadrant (u v : Plane) (acute : 0 < inner ℝ u v)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (inside : StrictQuadrant (a • u + b • v)) :
    StrictQuadrant u ∨ StrictQuadrant v := by
  change 0 < a * u 0 + b * v 0 ∧ 0 < a * u 1 + b * v 1 at inside
  have dot : 0 < u 0 * v 0 + u 1 * v 1 := by
    simpa only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply] using acute
  by_contra neither
  have left : u 0 ≤ 0 ∨ u 1 ≤ 0 := by
    simpa only [StrictQuadrant, not_and_or, not_lt] using (not_or.mp neither).1
  have right : v 0 ≤ 0 ∨ v 1 ≤ 0 := by
    simpa only [StrictQuadrant, not_and_or, not_lt] using (not_or.mp neither).2
  rcases left with ux | uy <;> rcases right with vx | vy
  · exact (not_lt_of_ge (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha ux)
      (mul_nonpos_of_nonneg_of_nonpos hb vx))) inside.1
  · have vx : 0 < v 0 := by
      by_contra nonpositive
      have bound := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha ux)
        (mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_gt nonpositive))
      exact (not_lt_of_ge bound) inside.1
    have uy : 0 < u 1 := by
      by_contra nonpositive
      have bound := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt nonpositive))
        (mul_nonpos_of_nonneg_of_nonpos hb vy)
      exact (not_lt_of_ge bound) inside.2
    exact (not_lt_of_ge (add_nonpos (mul_nonpos_of_nonpos_of_nonneg ux vx.le)
      (mul_nonpos_of_nonneg_of_nonpos uy.le vy))) dot
  · have ux : 0 < u 0 := by
      by_contra nonpositive
      have bound := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt nonpositive))
        (mul_nonpos_of_nonneg_of_nonpos hb vx)
      exact (not_lt_of_ge bound) inside.1
    have vy : 0 < v 1 := by
      by_contra nonpositive
      have bound := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha uy)
        (mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_gt nonpositive))
      exact (not_lt_of_ge bound) inside.2
    exact (not_lt_of_ge (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ux.le vx)
      (mul_nonpos_of_nonpos_of_nonneg uy vy.le))) dot
  · exact (not_lt_of_ge (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha uy)
      (mul_nonpos_of_nonneg_of_nonpos hb vy))) inside.2

/-- An actual input edge makes strict quadrant progress from an acute triangle corner. -/
theorem Triangle.exists_incident_quadrant_edge (T : Triangle) (i : Fin 3)
    (acute : T.cornerAngle i < Real.pi / 2) (p : Plane) (present : p ∈ T.carrier)
    (ahead : StrictQuadrant (p - T.vertex i)) :
    StrictQuadrant (T.vertex (Triangle.next i) - T.vertex i) ∨
      StrictQuadrant (T.vertex (Triangle.next (Triangle.next i)) - T.vertex i) := by
  let u := T.vertex (Triangle.next i) - T.vertex i
  let v := T.vertex (Triangle.next (Triangle.next i)) - T.vertex i
  have dot : 0 < inner ℝ u v := by
    apply lt_of_not_ge
    intro nonpositive
    exact (not_le_of_gt acute)
      (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp nonpositive)
  let a := T.coord (Triangle.next i) p
  let b := T.coord (Triangle.next (Triangle.next i)) p
  have coefficients := T.carrier_subset_cornerWedge i present
  have combination := T.reconstruct_corner i p
  change a • u + b • v + T.vertex i = p at combination
  have expression : a • u + b • v = p - T.vertex i := eq_sub_of_add_eq combination
  apply acute_generators_meet_quadrant u v dot a b coefficients.1 coefficients.2
  rwa [expression]

end Unfoldings
