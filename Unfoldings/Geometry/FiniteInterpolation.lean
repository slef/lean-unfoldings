module

public import Unfoldings.Geometry.ChainPaths
public import Mathlib.Topology.Order.IntermediateValue

/-! A finite sequence from zero to one covers the entire parameter interval by its links. -/

@[expose] public section

namespace Unfoldings

/-- Every parameter is interpolated on one actual link; no strict-order premise is needed. -/
theorem exists_finite_interpolation {n : ℕ} (parameter : Fin (n + 2) → unitInterval)
    (start : parameter 0 = 0) (finish : parameter (Fin.last (n + 1)) = 1)
    (u : unitInterval) :
    ∃ k : Fin (n + 1), ∃ t : unitInterval,
      AffineMap.lineMap (parameter k.castSucc).val (parameter k.succ).val t.val = u.val := by
  let P : PolygonalChain ℝ (n + 1) := ⟨fun j => (parameter j).val⟩
  have covered : Set.Icc (0 : ℝ) 1 ⊆ Set.range P.path := by
    simpa only [Path.source, Path.target, P, start, finish, Set.Icc.coe_zero, Set.Icc.coe_one] using
      intermediate_value_univ (0 : unitInterval) 1 P.path.continuous
  obtain ⟨s, at_u⟩ := covered u.property
  obtain ⟨k, t, at_s⟩ := P.path_point_covered (by omega) s
  exact ⟨k, t, at_s.symm.trans at_u⟩

end Unfoldings
