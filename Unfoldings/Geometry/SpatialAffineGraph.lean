module

public import Unfoldings.Geometry.SpatialTriangle
public import Unfoldings.Geometry.TriangleAffineEquiv
public import Unfoldings.Cap.VerticalProduct

/-! Every affine height plane admits actual rigid Euclidean coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A reference triangle for identifying the horizontal coordinates of a supporting plane. -/
def coordinateTriangle : Triangle where
  vertex := ![0, WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![0, 1]]
  nondegenerate := by norm_num [orient]

/-- An affine graph has a rigid planar parametrization with invertible horizontal projection.
These are genuine Euclidean coordinates, rather than a metric imposed on projected faces. -/
theorem exists_spatial_affine_graph (height : Plane →ᵃ[ℝ] ℝ) :
    ∃ (place : Plane →ᵃⁱ[ℝ] Space) (project : Plane ≃ᵃ[ℝ] Plane),
      (∀ x, Cap.horizontal (place x) = project x) ∧ (∀ x, place x 2 = height (project x)) := by
  let p : Fin 3 → Plane := coordinateTriangle.vertex
  let z : Fin 3 → Space := fun i => Cap.horizontalAtHeight (p i) (height (p i))
  have genuine : (inner ℝ (z 1 - z 0) (z 2 - z 0)) ^ 2 <
      ‖z 1 - z 0‖ ^ 2 * ‖z 2 - z 0‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply,
      PiLp.sub_apply, z, p, coordinateTriangle, Cap.horizontalAtHeight]
    simp
    nlinarith [sq_nonneg (height (p 1) - height (p 0)),
      sq_nonneg (height (p 2) - height (p 0))]
  obtain ⟨T, place, first, middle, last⟩ := exists_spatial_triangle (z 0) (z 1) (z 2) genuine
  let project := T.cornerEquiv coordinateTriangle
  have vertices (i : Fin 3) : place (T.vertex i) = z i := by
    fin_cases i
    · exact first
    · exact middle
    · exact last
  have horizontal : Cap.horizontal.toAffineMap.comp place.toAffineMap = project.toAffineMap := by
    apply T.affine_ext
    intro i
    change Cap.horizontal (place (T.vertex i)) = project (T.vertex i)
    rw [vertices, Triangle.cornerEquiv_vertex]
    exact Cap.horizontal_horizontalAtHeight _ _
  have vertical : (EuclideanSpace.proj 2).toLinearMap.toAffineMap.comp place.toAffineMap =
      height.comp project.toAffineMap := by
    apply T.affine_ext
    intro i
    change place (T.vertex i) 2 = height (project (T.vertex i))
    rw [vertices, Triangle.cornerEquiv_vertex]
    rfl
  exact ⟨place, project, fun x => congrArg (fun A : Plane →ᵃ[ℝ] Plane => A x) horizontal,
    fun x => congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A x) vertical⟩

end Unfoldings
