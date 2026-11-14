module

public import Unfoldings.Geometry.ChainPaths

/-! Linear supporting inequalities on the whole chain follow from its actual vertices. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (source : E) (height : E →ₗ[ℝ] ℝ)

theorem height_point (i : Fin n) (t : unitInterval) :
    height (P.point i t - source) =
      (1 - (t : ℝ)) * height (P.vertex i.castSucc - source) +
        (t : ℝ) * height (P.vertex i.succ - source) := by
  simp only [point, AffineMap.lineMap_apply_module', map_add, map_sub, map_smul, smul_eq_mul]
  ring

/-- Closed supporting halfplanes contain every actual link, including collapsed links. -/
theorem height_nonneg_on_path (vertices : ∀ j, 0 ≤ height (P.vertex j - source))
    {z : E} (member : z ∈ Set.range P.path) : 0 ≤ height (z - source) := by
  rw [P.path_range] at member
  rcases member with initial | member
  · rw [Set.mem_singleton_iff.mp initial]
    exact vertices 0
  · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp member
    rw [P.height_point source height]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (vertices i.castSucc))
      (mul_nonneg t.property.1 (vertices i.succ))

/-- Strict vertex support remains strict at every point of every actual link. -/
theorem height_pos_on_path (vertices : ∀ j, 0 < height (P.vertex j - source))
    {z : E} (member : z ∈ Set.range P.path) : 0 < height (z - source) := by
  rw [P.path_range] at member
  rcases member with initial | member
  · rw [Set.mem_singleton_iff.mp initial]
    exact vertices 0
  · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp member
    rw [P.height_point source height]
    rcases lt_or_eq_of_le t.property.2 with strict | same
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr strict) (vertices i.castSucc))
        (mul_nonneg t.property.1 (vertices i.succ).le)
    · rw [same, sub_self, zero_mul, one_mul, zero_add]
      exact vertices i.succ

end Unfoldings.PolygonalChain
