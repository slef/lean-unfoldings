module

public import Unfoldings.Roof.SectorDevelopment

/-! Actual projected parent segments are the original selected seam edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

/-- The directed parent segment uses the whole actual original edge, in either endpoint order. -/
theorem parent_segment_eq_original_seam
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    segment ℝ (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val)) =
      (K.projectedTriangle (C.left (M.selection.edge e)).face).edge
        (C.left (M.selection.edge e)).edge := by
  rcases M.selection.link e with first | last
  · rw [first.2, first.1]
    rfl
  · rw [last.2, last.1]
    exact segment_symm ℝ _ _

end Unfoldings.ConvexRoof.SectorForest
