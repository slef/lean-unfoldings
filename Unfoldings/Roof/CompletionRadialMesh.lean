module

public import Unfoldings.Roof.CompletionSkirtSeeds
public import Unfoldings.Roof.CompletionPrescribedSegments

/-! Construct the actual whole-edge mesh of the previously chosen exterior radial components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {J : Type u}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- Choose the seeds first, then mesh every genuine radial component and original edge. -/
def radialMesh {q : Plane} (origin : q ∈ interior K.footprint) :
    let F := E.cornerTails origin
    K.CompletionMesh φ region (K.originalAndSegmentEquations F.first F.last F.different) := by
  let F := E.cornerTails origin
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  exact E.alignToLines _ (K.originalAndSegmentEquations_ne_zero F.first F.last F.different)

/-- The meshed component is exactly a union of actual whole fine edges. -/
theorem radialMesh_component_cover {q : Plane} (origin : q ∈ interior K.footprint)
    (c : (E.cornerTails origin).Active) :
    let F := E.cornerTails origin
    let L := E.radialMesh origin
    (F.componentTail c.val).carrier =
      ⋃ e : {e : L.mesh.Index × Fin 3 //
          (L.mesh.projectedTriangle e.1).edge e.2 ⊆ (F.componentTail c.val).carrier},
        (L.mesh.projectedTriangle e.val.1).edge e.val.2 :=
  (E.radialMesh origin).segment_eq_union_subedges c
    ((E.cornerTails origin).component_member c.val)
    ((E.cornerTails origin).component_tip_member c.val)

end Unfoldings.ConvexRoof.CompletionMesh
