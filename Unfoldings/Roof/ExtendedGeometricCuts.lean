module

public import Unfoldings.Roof.ParentSegments
public import Unfoldings.Roof.SkirtRadialCuts

/-! Actual original whole-edge cuts together with their exterior radial continuations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

def projectedCutCarrier : Set Plane :=
  ⋃ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    segment ℝ (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val))

theorem projectedVertex_mem_cutCarrier (v : C.Vertex Set.univ) (nonroot : v ∉ M.parents.roots) :
    K.projectedVertex v ∈ M.projectedCutCarrier :=
  Set.mem_iUnion.mpr ⟨⟨v, nonroot⟩, left_mem_segment ℝ _ _⟩

def extendedGeometricCuts {outer : Set Plane} {q : Plane} (F : K.SkirtTailFamily outer q) :
    Set Plane := M.projectedCutCarrier ∪ ⋃ c : F.Component, (F.componentTail c).carrier

end Unfoldings.ConvexRoof.SectorForest
