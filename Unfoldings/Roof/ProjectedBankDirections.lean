module

public import Unfoldings.Roof.Basic
public import Unfoldings.Polyhedron.ProjectedBoundaryChain

/-! Actual roof-bank directions remain genuine in horizontal projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Every original spatial edge germ has nonzero horizontal velocity on an upward roof. -/
theorem horizontal_germDirection_ne_zero (p : C.Germ) :
    Cap.horizontal (K.folding.germDirection p) ≠ 0 := by
  obtain ⟨direction, at_direction⟩ := K.folding.germDirection_mem_range p
  have tangent : inner ℝ (K.normal p.1.1) (K.folding.germDirection p) = 0 := by
    rw [← at_direction]
    exact K.normal_tangent _ _
  exact Cap.tangent_horizontal_ne_zero _ _ (K.normal_unit _) (K.normal_upward _)
    tangent (K.folding.germDirection_ne_zero p)

/-- No actual projected roof bank disappears, including the true final bank. -/
theorem projectedBoundaryChain_edge_ne_zero {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.folding.projectedBoundaryChain chain).edge i ≠ 0 := by
  rw [K.folding.projectedBoundaryChain_edge]
  exact K.horizontal_germDirection_ne_zero _

end Unfoldings.ConvexRoof
