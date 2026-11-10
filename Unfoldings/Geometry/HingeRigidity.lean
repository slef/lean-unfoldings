module

public import Unfoldings.Geometry.TriangleMotion
public import Mathlib.Geometry.Euclidean.Basic

/-! Two endpoint distances and a strict side determine a planar point and its hinge motion. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The two-circle ambiguity disappears after fixing a strict side of the centers' line. -/
theorem eq_of_dist_eq_of_same_side {a b x y : Plane} (noncollinear : orient a b x ≠ 0)
    (first : dist y a = dist x a) (last : dist y b = dist x b)
    (side : 0 < orient a b x * orient a b y) : y = x := by
  have different : a ≠ b := by
    intro equal
    exact noncollinear (by simp [orient, equal])
  let R := lineReflection a b
  have reflected_ne : x ≠ R x := by
    intro equal
    have equation := orient_lineReflection a b x
    rw [← equal] at equation
    exact noncollinear (by linarith)
  have at_a : dist (R x) a = dist x a := by
    calc
      dist (R x) a = dist (R x) (R a) := congrArg (dist (R x)) (lineReflection_left a b).symm
      _ = dist x a := R.isometry.dist_eq x a
  have at_b : dist (R x) b = dist x b := by
    calc
      dist (R x) b = dist (R x) (R b) := congrArg (dist (R x)) (lineReflection_right a b).symm
      _ = dist x b := R.isometry.dist_eq x b
  have dimension : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two dimension different
    reflected_ne rfl at_a first rfl at_b last with equal | reflected
  · exact equal
  · have opposite := orient_lineReflection a b x
    change orient a b (R x) = -orient a b x at opposite
    rw [reflected, opposite] at side
    nlinarith [sq_nonneg (orient a b x)]


/-- A whole joined edge and a strict common side determine the second face motion. -/
theorem rigid_eq_of_joined_edge_and_side (T U : Triangle) (e f : Fin 3)
    (identify : T.Edge e ≃ᵢ U.Edge f) (L A B : Plane ≃ᵃⁱ[ℝ] Plane)
    (joinedA : ∀ x : T.Edge e, L x.val = A (identify x).val)
    (joinedB : ∀ x : T.Edge e, L x.val = B (identify x).val)
    (side : 0 < orient (L (T.vertex e)) (L (T.vertex (Triangle.next e))) (A (U.opposite f)) *
      orient (L (T.vertex e)) (L (T.vertex (Triangle.next e))) (B (U.opposite f))) : A = B := by
  have distances (x : T.Edge e) : dist (B (U.opposite f)) (L x.val) =
      dist (A (U.opposite f)) (L x.val) := by
    calc
      dist (B (U.opposite f)) (L x.val) = dist (B (U.opposite f)) (B (identify x).val) :=
        congrArg (dist _) (joinedB x)
      _ = dist (U.opposite f) (identify x).val := B.isometry.dist_eq _ _
      _ = dist (A (U.opposite f)) (A (identify x).val) := (A.isometry.dist_eq _ _).symm
      _ = dist (A (U.opposite f)) (L x.val) := congrArg (dist _) (joinedA x).symm
  have nonzero : orient (L (T.vertex e)) (L (T.vertex (Triangle.next e)))
      (A (U.opposite f)) ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at side
    exact (lt_irrefl _ side)
  have third : B (U.opposite f) = A (U.opposite f) := eq_of_dist_eq_of_same_side nonzero
    (distances ⟨_, left_mem_segment ℝ _ _⟩) (distances ⟨_, right_mem_segment ℝ _ _⟩) side
  have along (y : U.Edge f) : A y.val = B y.val := by
    have first := joinedA (identify.symm y)
    have last := joinedB (identify.symm y)
    rw [identify.apply_symm_apply] at first last
    exact first.symm.trans last
  have equal : A.toAffineMap = B.toAffineMap := by
    apply U.affine_ext
    intro i
    rcases Triangle.corner_cases f i with rfl | rfl | rfl
    · exact along ⟨_, left_mem_segment ℝ _ _⟩
    · exact along ⟨_, right_mem_segment ℝ _ _⟩
    · exact third.symm
  apply AffineIsometryEquiv.ext
  intro x
  exact congrArg (fun h : Plane →ᵃ[ℝ] Plane => h x) equal

namespace Triangle

/-- Once an edge is fixed, its outward rigid face motion is unique. -/
theorem rigid_eq_of_edge_and_side (T : Triangle) (e : Fin 3) (A B : Plane ≃ᵃⁱ[ℝ] Plane)
    (first : A (T.vertex e) = B (T.vertex e))
    (last : A (T.vertex (next e)) = B (T.vertex (next e)))
    (side : 0 < orient (A (T.vertex e)) (A (T.vertex (next e))) (A (T.opposite e)) *
      orient (A (T.vertex e)) (A (T.vertex (next e))) (B (T.opposite e))) : A = B := by
  have third : B (T.opposite e) = A (T.opposite e) :=
    eq_of_dist_eq_of_same_side (orient_map_ne_zero A (T.orient_edge_ne_zero e))
      (by
        calc
          dist (B (T.opposite e)) (A (T.vertex e)) =
              dist (B (T.opposite e)) (B (T.vertex e)) := congrArg (dist _) first
          _ = dist (T.opposite e) (T.vertex e) := B.isometry.dist_eq _ _
          _ = dist (A (T.opposite e)) (A (T.vertex e)) := (A.isometry.dist_eq _ _).symm)
      (by
        calc
          dist (B (T.opposite e)) (A (T.vertex (next e))) =
              dist (B (T.opposite e)) (B (T.vertex (next e))) := congrArg (dist _) last
          _ = dist (T.opposite e) (T.vertex (next e)) := B.isometry.dist_eq _ _
          _ = dist (A (T.opposite e)) (A (T.vertex (next e))) :=
            (A.isometry.dist_eq _ _).symm) side
  have equal : A.toAffineMap = B.toAffineMap := by
    apply T.affine_ext
    intro i
    rcases corner_cases e i with rfl | rfl | rfl
    · exact first
    · exact last
    · exact third.symm
  apply AffineIsometryEquiv.ext
  intro x
  exact congrArg (fun h : Plane →ᵃ[ℝ] Plane => h x) equal

end Triangle
end Unfoldings
