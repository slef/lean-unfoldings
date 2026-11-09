module

public import Unfoldings.Geometry.SpatialPlane

/-! Distinct two-dimensional linear planes intersect in their common nonzero line. -/

@[expose] public section

namespace Unfoldings

theorem plane_inf_eq_span {U V : Submodule ℝ Space}
    (rank_u : Module.finrank ℝ U = 2) (rank_v : Module.finrank ℝ V = 2)
    (different : U ≠ V) {d : Space} (nonzero : d ≠ 0) (in_u : d ∈ U) (in_v : d ∈ V) :
    U ⊓ V = Submodule.span ℝ {d} := by
  have included : Submodule.span ℝ {d} ≤ U ⊓ V := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨in_u, in_v⟩
  have rank_le := Submodule.finrank_mono (show U ⊓ V ≤ U from inf_le_left)
  have rank_not_two : Module.finrank ℝ ↥(U ⊓ V) ≠ 2 := by
    intro equal
    have inf_eq := Submodule.eq_of_le_of_finrank_eq (show U ⊓ V ≤ U from inf_le_left)
      (equal.trans rank_u.symm)
    have contained : U ≤ V := by rw [← inf_eq]; exact inf_le_right
    exact different (Submodule.eq_of_le_of_finrank_eq contained (rank_u.trans rank_v.symm))
  have rank_span : Module.finrank ℝ (Submodule.span ℝ {d}) = 1 :=
    finrank_span_singleton nonzero
  have rank_ge := Submodule.finrank_mono included
  have rank_inf : Module.finrank ℝ ↥(U ⊓ V) = 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq included (rank_span.trans rank_inf.symm)).symm

end Unfoldings
