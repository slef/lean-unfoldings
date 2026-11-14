module

public import Unfoldings.Convex.SlopeEnvelope

/-! Exact active cells along exterior rays of a compact-slope conjugate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem affine_ray (p v u : Plane) (t : ℝ) :
    E.affine p (v + t • u) = E.affine p v + t * inner ℝ u p := by
  simp only [affine, inner_add_left, real_inner_smul_left]
  ring

/-- A maximizing boundary slope on a supporting side remains active on its outward ray. -/
theorem height_ray {p v u : Plane} {c t : ℝ} (active : E.Active v p)
    (side : inner ℝ u p = c) (support : ∀ q ∈ E.slopes, inner ℝ u q ≤ c)
    (time : 0 ≤ t) : E.height (v + t • u) = E.height v + t * c := by
  apply le_antisymm
  · apply E.height_le
    intro q hq
    rw [E.affine_ray]
    exact add_le_add (E.affine_le v hq) (mul_le_mul_of_nonneg_left (support q hq) time)
  · have lower := E.affine_le (v + t • u) active.1
    rw [E.affine_ray, side, ← active.2] at lower
    exact lower

/-- At every positive time the active cell is exactly the original cell intersected with
its assigned supporting side. In particular this cell is constant along the open ray. -/
theorem active_ray_iff {p v u q : Plane} {c t : ℝ} (active : E.Active v p)
    (side : inner ℝ u p = c) (support : ∀ r ∈ E.slopes, inner ℝ u r ≤ c)
    (time : 0 < t) :
    E.Active (v + t • u) q ↔ E.Active v q ∧ inner ℝ u q = c := by
  have ray := E.height_ray active side support time.le
  constructor
  · rintro ⟨hq, equal⟩
    rw [ray, E.affine_ray] at equal
    have before := E.affine_le v hq
    have bound := support q hq
    have on_side : inner ℝ u q = c := by nlinarith
    refine ⟨⟨hq, ?_⟩, on_side⟩
    nlinarith
  · rintro ⟨⟨hq, equal⟩, on_side⟩
    refine ⟨hq, ?_⟩
    rw [ray, E.affine_ray, equal, on_side]

/-- Boundary-slope potential associated with exactly the same dual cost. -/
def boundaryEnvelope (nonempty : (frontier E.slopes).Nonempty) : SlopeEnvelope where
  slopes := frontier E.slopes
  compact := E.compact.of_isClosed_subset isClosed_frontier E.compact.isClosed.frontier_subset
  nonempty := nonempty
  dual := E.dual
  continuous_dual := E.continuous_dual

theorem boundary_height_le (nonempty : (frontier E.slopes).Nonempty) (v : Plane) :
    (E.boundaryEnvelope nonempty).height v ≤ E.height v := by
  apply (E.boundaryEnvelope nonempty).height_le
  intro p hp
  exact E.affine_le v (E.compact.isClosed.frontier_subset hp)

theorem active_boundary (nonempty : (frontier E.slopes).Nonempty) {v p : Plane}
    (active : E.Active v p) (boundary : p ∈ frontier E.slopes) :
    (E.boundaryEnvelope nonempty).Active v p := by
  refine ⟨boundary, le_antisymm ?_ ?_⟩
  · exact (E.boundary_height_le nonempty v).trans active.2.le
  · exact (E.boundaryEnvelope nonempty).affine_le v boundary

/-- The extension and its boundary potential agree along the entire safe exterior ray. -/
theorem boundary_height_ray {p v u : Plane} {c t : ℝ} (active : E.Active v p)
    (boundary : p ∈ frontier E.slopes) (side : inner ℝ u p = c)
    (support : ∀ q ∈ E.slopes, inner ℝ u q ≤ c) (time : 0 ≤ t) :
    (E.boundaryEnvelope ⟨p, boundary⟩).height (v + t • u) =
      E.height (v + t • u) := by
  let B := E.boundaryEnvelope ⟨p, boundary⟩
  have activeB := E.active_boundary ⟨p, boundary⟩ active boundary
  have equal : B.height v = E.height v := activeB.2.trans active.2.symm
  have supportB : ∀ q ∈ B.slopes, inner ℝ u q ≤ c :=
    fun q hq => support q (E.compact.isClosed.frontier_subset hq)
  rw [B.height_ray activeB side supportB time, E.height_ray active side support time, equal]

end Unfoldings.SlopeEnvelope
