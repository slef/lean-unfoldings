module

public import Unfoldings.Geometry.EdgeSides

/-! Genuine interior points occur arbitrarily close to every closed triangle point. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem exists_near_interior_ne (T : Triangle) {p : Plane} (member : p ∈ T.carrier)
    {r : ℝ} (positive : 0 < r) :
    ∃ q ∈ interior T.carrier, dist q p < r ∧ q ≠ p := by
  have closure_interior := T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    T.interior_nonempty
  rw [T.compact_carrier.isClosed.closure_eq] at closure_interior
  have in_closure : p ∈ closure (interior T.carrier) := closure_interior.symm ▸ member
  obtain ⟨w, inside, close⟩ := Metric.mem_closure_iff.mp in_closure r positive
  have patch : (interior T.carrier ∩ Metric.ball p r).Nonempty :=
    ⟨w, inside, by simpa only [Metric.mem_ball, dist_comm] using close⟩
  obtain ⟨q, different, near⟩ := (dense_compl_singleton p).exists_mem_open
    (isOpen_interior.inter Metric.isOpen_ball) patch
  exact ⟨q, near.1, near.2, different⟩

end Unfoldings.Triangle
