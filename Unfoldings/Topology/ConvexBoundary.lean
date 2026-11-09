module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Sphere topology of bounded convex boundaries, independent of triangle complexes. -/

@[expose] public section

noncomputable section

namespace Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/-- The boundary of a bounded convex body with interior is homeomorphic to the unit sphere. -/
theorem exists_homeomorph_frontier_sphere (convex : Convex ℝ s)
    (inside : (interior s).Nonempty) (bounded : Bornology.IsBounded s) :
    Nonempty (frontier s ≃ₜ Metric.sphere (0 : E) 1) := by
  obtain ⟨h, _, _, boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex inside bounded
  exact ⟨(h.image (frontier s)).trans (Homeomorph.setCongr boundary)⟩

/-- A bounded convex body's boundary is connected in dimension greater than one. -/
theorem frontier_connectedSpace (convex : Convex ℝ s) (inside : (interior s).Nonempty)
    (bounded : Bornology.IsBounded s) (dimension : 1 < Module.rank ℝ E) :
    ConnectedSpace (frontier s) := by
  obtain ⟨h⟩ := convex.exists_homeomorph_frontier_sphere inside bounded
  let : ConnectedSpace (Metric.sphere (0 : E) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere dimension 0 zero_le_one)
  exact h.symm.surjective.connectedSpace h.symm.continuous

end Convex
