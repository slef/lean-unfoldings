module

public import Unfoldings.Geometry.Barycentric
public import Mathlib.Geometry.Euclidean.Triangle

/-! Positive Euclidean corner angles of the actual nondegenerate triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

open EuclideanGeometry

/-- The interior angle between the two incident triangle edges, measured in radians. -/
def cornerAngle (T : Triangle) (i : Fin 3) : ℝ :=
  angle (T.vertex (next i)) (T.vertex i) (T.vertex (next (next i)))

theorem not_collinear_corners (T : Triangle) (i : Fin 3) :
    ¬ Collinear ℝ ({T.vertex (next i), T.vertex i, T.vertex (next (next i))} : Set Plane) := by
  have vertices : ({T.vertex (next i), T.vertex i, T.vertex (next (next i))} : Set Plane) =
      Set.range T.vertex := by
    ext p
    constructor
    · rintro (rfl | rfl | h)
      · exact ⟨next i, rfl⟩
      · exact ⟨i, rfl⟩
      · exact ⟨next (next i), h.symm⟩
    · rintro ⟨j, rfl⟩
      rcases corner_cases i j with rfl | rfl | rfl <;> simp
  rw [vertices]
  exact affineIndependent_iff_not_collinear.mp T.affineIndependent_vertices

theorem cornerAngle_pos (T : Triangle) (i : Fin 3) : 0 < T.cornerAngle i :=
  angle_pos_of_not_collinear (T.not_collinear_corners i)

theorem cornerAngle_lt_pi (T : Triangle) (i : Fin 3) : T.cornerAngle i < Real.pi :=
  angle_lt_pi_of_not_collinear (T.not_collinear_corners i)

theorem sum_cornerAngle (T : Triangle) : ∑ i : Fin 3, T.cornerAngle i = Real.pi := by
  have sum := angle_add_angle_add_angle_eq_pi (T.vertex 2) (T.edge_endpoints_ne 0).symm
  change angle (T.vertex 0) (T.vertex 1) (T.vertex 2) +
    angle (T.vertex 1) (T.vertex 2) (T.vertex 0) +
      angle (T.vertex 2) (T.vertex 0) (T.vertex 1) = Real.pi at sum
  simp only [Fin.sum_univ_succ]
  change angle (T.vertex 1) (T.vertex 0) (T.vertex 2) +
    (angle (T.vertex 2) (T.vertex 1) (T.vertex 0) +
      (angle (T.vertex 0) (T.vertex 2) (T.vertex 1) + 0)) = Real.pi
  linarith [angle_comm (T.vertex 0) (T.vertex 1) (T.vertex 2),
    angle_comm (T.vertex 1) (T.vertex 2) (T.vertex 0),
    angle_comm (T.vertex 2) (T.vertex 0) (T.vertex 1)]

end Unfoldings.Triangle
