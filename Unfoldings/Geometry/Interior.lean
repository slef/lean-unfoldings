module

public import Unfoldings.Geometry.Halfplane
public import Mathlib.Tactic.Linarith

/-! Triangle interiors have positive clearance from every edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem not_mem_interior_of_upper_bound {A : Set Plane} (height : Plane →L[ℝ] ℝ)
    (surjective : Function.Surjective height) (level : ℝ)
    (upper : ∀ x ∈ A, height x ≤ level) {x : Plane} (equal : height x = level) :
    x ∉ interior A := by
  have inclusion : A ⊆ height ⁻¹' Set.Iic level := upper
  have strict := interior_mono inclusion
  rw [height.interior_preimage surjective, interior_Iic] at strict
  intro hx
  exact (not_lt_of_ge equal.ge) (strict hx)

theorem not_mem_interior_of_lower_bound {A : Set Plane} (height : Plane →L[ℝ] ℝ)
    (surjective : Function.Surjective height) (level : ℝ)
    (lower : ∀ x ∈ A, level ≤ height x) {x : Plane} (equal : height x = level) :
    x ∉ interior A := by
  have inclusion : A ⊆ height ⁻¹' Set.Ici level := lower
  have strict := interior_mono inclusion
  rw [height.interior_preimage surjective, interior_Ici] at strict
  intro hx
  exact (not_lt_of_ge equal.le) (strict hx)

namespace Triangle

theorem not_mem_interior_of_mem_edge (T : Triangle) (e : Fin 3) {x : Plane}
    (hx : x ∈ T.edge e) : x ∉ interior T.carrier := by
  let height := lineHeight (T.vertex e) (T.vertex (next e))
  let level := height (T.vertex e)
  have surjective : Function.Surjective height := lineHeight_surjective (T.orient_edge_ne_zero e)
  have along : ∀ y : T.Edge e, height y = level := by
    intro y
    apply sub_eq_zero.mp
    exact (orient_eq_height _ _ _).symm.trans (orient_eq_zero_of_mem_segment y.property)
  rcases lt_or_gt_of_ne (T.orient_edge_ne_zero e) with negative | positive
  · have third : height (T.opposite e) ≤ level := by
      rw [← sub_nonpos, ← orient_eq_height]
      exact negative.le
    have corners := T.vertices_le_of_edge (AffineMap.id ℝ Plane) e height level along third
    apply not_mem_interior_of_upper_bound height surjective level
      (fun y hy => T.image_le_of_vertices (AffineMap.id ℝ Plane) height level corners y
        ⟨y, hy, rfl⟩)
    exact along ⟨x, hx⟩
  · have third : level ≤ height (T.opposite e) := by
      rw [← sub_nonneg, ← orient_eq_height]
      exact positive.le
    have corners := T.vertices_ge_of_edge (AffineMap.id ℝ Plane) e height level along third
    apply not_mem_interior_of_lower_bound height surjective level
      (fun y hy => T.image_ge_of_vertices (AffineMap.id ℝ Plane) height level corners y
        ⟨y, hy, rfl⟩)
    exact along ⟨x, hx⟩

/-- Every face-interior point has a Euclidean ball with triple-radius edge clearance. -/
theorem exists_radius_clear_edges (T : Triangle) (p : T.Cell)
    (inside : p.val ∈ interior T.carrier) :
    ∃ r > 0, Metric.ball p.val r ⊆ T.carrier ∧
      ∀ e, ∀ x ∈ T.edge e, 3 * r ≤ dist x p.val := by
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp isOpen_interior p.val inside
  refine ⟨ε / 3, div_pos positive (by norm_num), ?_, ?_⟩
  · intro x hx
    apply interior_subset (ball ?_)
    apply Metric.mem_ball.mpr
    have near := Metric.mem_ball.mp hx
    linarith
  · intro e x hx
    by_contra close
    have near : dist x p.val < ε := by
      have h := lt_of_not_ge close
      linarith
    exact T.not_mem_interior_of_mem_edge e hx (ball (Metric.mem_ball.mpr near))

/-- A planar ball in the carrier has the same metric as the corresponding cell ball. -/
def cellBallIsometry (T : Triangle) (p : T.Cell) (r : ℝ)
    (included : Metric.ball p.val r ⊆ T.carrier) : Metric.ball p.val r ≃ᵢ Metric.ball p r where
  toEquiv :=
    { toFun := fun x => ⟨⟨x.val, included x.property⟩, by
        apply Metric.mem_ball.mpr
        exact Metric.mem_ball.mp x.property⟩
      invFun := fun x => ⟨x.val.val, by
        apply Metric.mem_ball.mpr
        exact Metric.mem_ball.mp x.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  isometry_toFun := fun _ _ => rfl

end Triangle
end Unfoldings
