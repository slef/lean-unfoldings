module

public import Unfoldings.Convex.SphericalPolygonSides

/-! A spherical selector has named supporting planes and the actual minor arcs on them. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- Present a selector with one inward linear form and one genuine side per index. -/
structure SphericalSelectorBoundary (J : Type*) (region : Set Space) where
  endpoint : J → Bool → Space
  form : J → Space →ₗ[ℝ] ℝ
  form_ne_zero : ∀ j, form j ≠ 0
  membership : ∀ x, x ∈ region ↔ ‖x‖ = 1 ∧ ∀ j, 0 ≤ form j x
  activeSide : ∀ j, {x ∈ region | form j x = 0} = closedMinorArc (endpoint j false) (endpoint j true)

namespace SphericalSelectorBoundary

variable {J : Type*} {region : Set Space} (B : SphericalSelectorBoundary J region)

include B in
theorem isClosed : IsClosed region := by
  have eq : region = Metric.sphere (0 : Space) 1 ∩ ⋂ j, {x | 0 ≤ B.form j x} := by
    ext x
    simp only [B.membership, Metric.mem_sphere, dist_zero_right, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
  rw [eq]
  exact Metric.isClosed_sphere.inter (isClosed_iInter fun j =>
    isClosed_le continuous_const (B.form j).continuous_of_finiteDimensional)

include B in
theorem sphericalConvex : SphericalConvex region := by
  refine ⟨fun x hx => ((B.membership x).mp hx).1, ?_⟩
  intro u hu v hv a b ha hb genuine
  refine (B.membership _).mpr ⟨NormedSpace.norm_normalize genuine, fun j => ?_⟩
  have first := ((B.membership u).mp hu).2 j
  have second := ((B.membership v).mp hv).2 j
  rw [NormedSpace.normalize, map_smul, map_add, map_smul, map_smul]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (add_nonneg (mul_nonneg ha first) (mul_nonneg hb second))

theorem side_mem {j : J} {x : Space} :
    x ∈ closedMinorArc (B.endpoint j false) (B.endpoint j true) ↔ x ∈ region ∧ B.form j x = 0 := by
  rw [← B.activeSide]
  rfl

theorem endpoint_mem (j : J) (b : Bool) : B.endpoint j b ∈ region := by
  cases b
  · exact (B.side_mem.mp (Set.mem_insert _ _)).1
  · exact (B.side_mem.mp (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).1

theorem endpoint_unit (j : J) (b : Bool) : ‖B.endpoint j b‖ = 1 :=
  ((B.membership _).mp (B.endpoint_mem j b)).1

end SphericalSelectorBoundary
end Unfoldings.FewestNets
