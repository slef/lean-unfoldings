module

public import Unfoldings.Examples.Tetrahedron.Boundary
public import Unfoldings.Source.Unfolding

/-! Instantiate the complete source-unfolding theorem at an actual tetrahedron edge midpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples.Tetrahedron

def sourceCell : (triangle 3).Cell :=
  (triangle 3).edgeMap 0
    ⟨midpoint ℝ ((triangle 3).vertex 0) ((triangle 3).vertex 1), midpoint_mem_segment _ _⟩

def source : complex.Realization Set.univ := complex.faceMap Set.univ 3 sourceCell

theorem source_spatial : folding.toSpace Set.univ source = vec3 (1 / 2) 0 0 := by
  unfold source
  rw [folding.toSpace_faceMap]
  change placement 3 sourceCell.val = _
  ext i
  fin_cases i <;>
    norm_num [sourceCell, Triangle.edgeMap,
      placement, linearIsometry, linear, triangle, vec2, vec3, midpoint_eq_smul_add]

theorem source_nonextreme :
    folding.toSpace Set.univ source ∉ folding.vertexHull.extremePoints ℝ := by
  rw [vertexHull_eq]
  intro extreme
  obtain ⟨i, equal⟩ := extremePoints_convexHull_subset extreme
  rw [source_spatial] at equal
  have first := congrArg (fun p : Space => p 0) equal
  fin_cases i <;> norm_num [vertex, vec3] at first

def sourceUnfolding :
    letI := convexBoundary.metricSpace
    SourceUnfolding (C := complex) source :=
  convexBoundary.sourceUnfoldingOfNonextreme source source_nonextreme

theorem sourceUnfolding_nonoverlapping :
    letI := convexBoundary.metricSpace
    sourceUnfolding.layout.Nonoverlapping := by
  let := convexBoundary.metricSpace
  exact sourceUnfolding.nonoverlapping

end Unfoldings.Examples.Tetrahedron
