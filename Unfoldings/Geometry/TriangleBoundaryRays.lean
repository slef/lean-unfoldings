module

public import Unfoldings.Geometry.TriangleFanBoundary
public import Unfoldings.Geometry.Angles
public import Unfoldings.Geometry.Endpoints

/-! Actual boundary rays at an original triangle corner recover precisely its original angle. -/

@[expose] public section

namespace Unfoldings

theorem exists_pos_smul_sub_of_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b x : E} (member : x ∈ segment ℝ a b) (different : x ≠ a) :
    ∃ t : ℝ, 0 < t ∧ x - a = t • (b - a) := by
  rw [segment_eq_image_lineMap] at member
  obtain ⟨t, bounds, rfl⟩ := member
  have positive : 0 < t := by
    apply lt_of_le_of_ne bounds.1
    intro zero
    apply different
    rw [← zero, AffineMap.lineMap_apply_zero]
  refine ⟨t, positive, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  abel

namespace Triangle

/-- A genuine frontier segment at a triangle corner follows one of its original rays. -/
theorem boundary_ray_from_corner (T : Triangle) (i : Fin 3) {x : Plane}
    (boundary : segment ℝ (T.vertex i) x ⊆ frontier T.carrier) (different : x ≠ T.vertex i) :
    (∃ t : ℝ, 0 < t ∧ x - T.vertex i = t • (T.vertex (next i) - T.vertex i)) ∨
      (∃ t : ℝ, 0 < t ∧ x - T.vertex i =
        t • (T.vertex (next (next i)) - T.vertex i)) := by
  obtain ⟨e, contained⟩ := T.boundary_segment_subset_edge boundary
  have apex := contained (left_mem_segment ℝ _ _)
  have terminal := contained (right_mem_segment ℝ _ _)
  rcases (T.edge_vertex_iff e ⟨T.vertex i, apex⟩).mp ⟨i, rfl⟩ with first | last
  · have same := T.vertex_injective first
    subst i
    exact Or.inl (exists_pos_smul_sub_of_mem_segment terminal different)
  · have same := T.vertex_injective last
    subst i
    right
    have cycle : next (next (next e)) = e := by fin_cases e <;> rfl
    rw [cycle]
    change x ∈ segment ℝ (T.vertex e) (T.vertex (next e)) at terminal
    rw [segment_symm] at terminal
    exact exists_pos_smul_sub_of_mem_segment terminal different

/-- Distinct actual frontier directions at a corner have exactly the triangle's corner angle. -/
theorem angle_boundary_rays_eq_cornerAngle (T : Triangle) (i : Fin 3) {x y : Plane}
    (first : segment ℝ (T.vertex i) x ⊆ frontier T.carrier)
    (last : segment ℝ (T.vertex i) y ⊆ frontier T.carrier)
    (xne : x ≠ T.vertex i) (yne : y ≠ T.vertex i)
    (different : InnerProductGeometry.angle (x - T.vertex i) (y - T.vertex i) ≠ 0) :
    InnerProductGeometry.angle (x - T.vertex i) (y - T.vertex i) = T.cornerAngle i := by
  have u_ne : T.vertex (next i) - T.vertex i ≠ 0 :=
    sub_ne_zero.mpr (T.edge_endpoints_ne i).symm
  have v_ne : T.vertex (next (next i)) - T.vertex i ≠ 0 := by
    apply sub_ne_zero.mpr
    apply T.vertex_injective.ne
    fin_cases i <;> decide
  rcases T.boundary_ray_from_corner i first xne with ⟨r, rp, xr⟩ | ⟨r, rp, xr⟩
  all_goals
    rcases T.boundary_ray_from_corner i last yne with ⟨s, sp, ys⟩ | ⟨s, sp, ys⟩
    all_goals
      rw [xr, ys, InnerProductGeometry.angle_smul_left_of_pos _ _ rp,
        InnerProductGeometry.angle_smul_right_of_pos _ _ sp] at different ⊢
  · exact (different (InnerProductGeometry.angle_self u_ne)).elim
  · rfl
  · exact InnerProductGeometry.angle_comm _ _
  · exact (different (InnerProductGeometry.angle_self v_ne)).elim

end Triangle
end Unfoldings
