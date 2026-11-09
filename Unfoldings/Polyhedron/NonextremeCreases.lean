module

public import Unfoldings.Polyhedron.NonextremeAxis
public import Unfoldings.Polyhedron.GermDirections

/-! Every genuine crease at a nonextreme vertex lies along one common axis. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_nonextreme_crease_axis (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    ∃ d : Space, d ≠ 0 ∧ ∀ p : C.LinkGerm Set.univ v,
      LinearMap.range (F.place p.val.1.1).linear ≠
        LinearMap.range (F.place (C.linkMate Set.univ v p).val.1.1).linear →
      d ∈ Submodule.span ℝ {F.germDirection p.val} := by
  obtain ⟨d, nonzero, planes⟩ := P.exists_axis_of_nonextreme v not_extreme
  refine ⟨d, nonzero, ?_⟩
  intro p different
  exact F.mem_span_germDirection_of_mate_planes Set.univ p.val different
    (planes ⟨p.val.1, p.property⟩)
    (planes ⟨(C.linkMate Set.univ v p).val.1, (C.linkMate Set.univ v p).property⟩)

end Unfoldings.SpatialFolding.ConvexBoundary
