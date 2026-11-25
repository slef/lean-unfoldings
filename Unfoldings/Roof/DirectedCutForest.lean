module

public import Unfoldings.Roof.PotentialCutForest

/-! A supplied directed seam forest has a geometric vertex potential. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) (parents : AscendingParents (C.Vertex Set.univ))

open Classical in
/-- Extend a parent order from the embedded vertices to a function on the
plane. Only its values at vertices enter the cut forest. -/
def cutVertexPotential (x : Plane) : ℝ :=
  if h : ∃ v, K.projectedVertex v = x then parents.height h.choose else 0

@[simp] theorem cutVertexPotential_projectedVertex (v : C.Vertex Set.univ) :
    K.cutVertexPotential parents (K.projectedVertex v) = parents.height v := by
  have exists_vertex : ∃ w, K.projectedVertex w = K.projectedVertex v := ⟨v, rfl⟩
  unfold cutVertexPotential
  rw [dite_eq_left exists_vertex]
  exact congrArg parents.height (K.projectedVertex_injective exists_vertex.choose_spec)

/-- The cut-disk construction can use an already oriented fine forest. A
convex potential is unnecessary once the actual directed seams are known. -/
def potentialCutForestOfParents (cuts : Set Plane)
    (roots_eq : parents.roots = {v | C.IsBoundaryVertex Set.univ v ∨ K.projectedVertex v ∉ cuts})
    (selection : parents.EdgeSelection C.seamGraph)
    (contains : ∀ e, (K.projectedTriangle (C.left (selection.edge e)).face).edge
      (C.left (selection.edge e)).edge ⊆ cuts) :
    K.PotentialCutForest (K.cutVertexPotential parents) cuts where
  parents := parents
  roots_eq := roots_eq
  height_eq := funext fun v => (K.cutVertexPotential_projectedVertex parents v).symm
  selection := selection
  selected_subset := contains

end Unfoldings.ConvexRoof
