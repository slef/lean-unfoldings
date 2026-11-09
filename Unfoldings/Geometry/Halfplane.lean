module

public import Unfoldings.Geometry.Edge
public import Unfoldings.Geometry.Separation

/-! Supporting heights and corner bounds for triangle edges. -/

@[expose] public section

namespace Unfoldings

/-- A continuous linear height whose level lines are parallel to the directed line `ab`. -/
noncomputable def lineHeight (a b : Plane) : Plane →L[ℝ] ℝ :=
  (b 0 - a 0) • EuclideanSpace.proj 1 - (b 1 - a 1) • EuclideanSpace.proj 0

theorem orient_eq_height (a b c : Plane) :
    orient a b c = lineHeight a b c - lineHeight a b a := by
  simp [orient, lineHeight]
  ring

theorem lineHeight_surjective {a b c : Plane} (noncollinear : orient a b c ≠ 0) :
    Function.Surjective (lineHeight a b) := by
  have nonzero : lineHeight a b (c - a) ≠ 0 := by
    rw [map_sub, ← orient_eq_height]
    exact noncollinear
  intro r
  refine ⟨(r / lineHeight a b (c - a)) • (c - a), ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ r nonzero

namespace Triangle

theorem vertices_le_of_edge (T : Triangle) (place : Plane →ᵃ[ℝ] Plane)
    (e : Fin 3) (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (along : ∀ x : T.Edge e, height (place x) = level)
    (third : height (place (T.opposite e)) ≤ level) :
    ∀ i, height (place (T.vertex i)) ≤ level := by
  intro i
  rcases corner_cases e i with rfl | rfl | rfl
  · exact (along ⟨_, left_mem_segment ℝ _ _⟩).le
  · exact (along ⟨_, right_mem_segment ℝ _ _⟩).le
  · exact third

theorem vertices_ge_of_edge (T : Triangle) (place : Plane →ᵃ[ℝ] Plane)
    (e : Fin 3) (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (along : ∀ x : T.Edge e, height (place x) = level)
    (third : level ≤ height (place (T.opposite e))) :
    ∀ i, level ≤ height (place (T.vertex i)) := by
  intro i
  rcases corner_cases e i with rfl | rfl | rfl
  · exact (along ⟨_, left_mem_segment ℝ _ _⟩).ge
  · exact (along ⟨_, right_mem_segment ℝ _ _⟩).ge
  · exact third

end Triangle

end Unfoldings
