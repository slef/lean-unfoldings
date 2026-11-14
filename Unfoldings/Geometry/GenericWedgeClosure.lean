module

public import Unfoldings.Geometry.GenericRadialSource
public import Unfoldings.Geometry.LinearPathBounds
public import Unfoldings.Geometry.RayAvoidance

/-! Construct actual radial-wedge Jordan closures with generic closing links. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n) (source : Plane)

/-- The closing point can avoid every prescribed finite family of nonzero affine equations. -/
theorem exists_generic_radial_wedge_closure {ι : Type*} [Finite ι]
    (radial : P.RadialFrom source 0) (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane)
    (inside : ∀ z ∈ Set.range P.path,
      0 ≤ (frame.symm (z - source)).1 ∧ 0 ≤ (frame.symm (z - source)).2)
    (equation : ι → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0) :
    ∃ c : Plane, (∀ i, equation i c ≠ 0) ∧
      ((frame.symm (c - source)).1 < 0 ∨ (frame.symm (c - source)).2 < 0) ∧
      0 < inner ℝ (P.vertex (Fin.last n) - source) (c - P.vertex (Fin.last n)) ∧
      Schoenflies.IsJordanCurve (Set.range P.path ∪
        ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c source) ∪
          segment ℝ source (P.vertex 0))) := by
  let b := P.vertex (Fin.last n)
  have nonzero : b - source ≠ 0 := by
    intro same
    have at_source := sub_eq_zero.mp same
    change dist source (P.vertex 0) < dist source b at progress
    rw [at_source, dist_self] at progress
    linarith
  obtain ⟨height, supporting, direction, negative, outward_direction⟩ :=
    exists_wedge_closing_direction frame (b - source) nonzero (inside b ⟨1, P.path.target⟩)
  obtain ⟨t, positive, outward⟩ := exists_outward_closing_point source b direction outward_direction
  let U : Set Plane := {c | height (c - source) < 0 ∧ 0 < inner ℝ (b - source) (c - b)}
  have continuous_height : Continuous height := height.continuous_of_finiteDimensional
  have continuous_outward : Continuous (fun c : Plane => inner ℝ (b - source) (c - b)) := by
    fun_prop
  have open_U : IsOpen U :=
    (isOpen_lt (continuous_height.comp (continuous_id.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_const continuous_outward)
  have in_U : source + t • direction ∈ U := by
    refine ⟨?_, outward⟩
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul] using
      mul_neg_of_pos_of_neg positive negative
  obtain ⟨c, member, regular⟩ :=
    (AffineArrangement.dense_regular equation proper).inter_open_nonempty
    U open_U ⟨source + t • direction, in_U⟩
  have excluded : (frame.symm (c - source)).1 < 0 ∨ (frame.symm (c - source)).2 < 0 := by
    by_cases first : (frame.symm (c - source)).1 < 0
    · exact Or.inl first
    · right
      by_contra second
      exact not_le_of_gt member.1
        (supporting (c - source) (le_of_not_gt first) (le_of_not_gt second))
  exact ⟨c, regular, excluded, member.2,
    P.radial_halfplane_closure_jordan source radial initial progress height
      (fun z hz => supporting (z - source) (inside z hz).1 (inside z hz).2) c member.1 member.2⟩

end Unfoldings.PolygonalChain
