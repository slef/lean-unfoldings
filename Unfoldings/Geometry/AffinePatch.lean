module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! Local agreement on a full-dimensional convex physical piece determines the whole affine map. -/

@[expose] public section

namespace Unfoldings

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-- Boundary centers are allowed: a full convex cell has interior points in every neighborhood. -/
theorem affine_eq_on_convex_patch {s : Set E} (convex : Convex ℝ s)
    (full : (interior s).Nonempty) {x : E} (member : x ∈ s)
    {r : ℝ} (positive : 0 < r) (f g : E →ᵃ[ℝ] V)
    (agrees : ∀ z ∈ s, dist z x < r → f z = g z) : f = g := by
  have approached : x ∈ closure (interior s) := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
    exact subset_closure member
  obtain ⟨y, inside, near⟩ := Metric.mem_closure_iff.mp approached r positive
  have patch_full : (interior (s ∩ Metric.ball x r)).Nonempty := by
    refine ⟨y, ?_⟩
    rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact ⟨inside, Metric.mem_ball.mpr (by rwa [dist_comm])⟩
  apply AffineMap.ext_on (isOpen_interior.affineSpan_eq_top patch_full)
  intro z hz
  exact agrees z (interior_subset hz).1 (interior_subset hz).2

end Unfoldings
