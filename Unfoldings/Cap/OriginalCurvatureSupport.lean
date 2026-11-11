module

public import Unfoldings.Cap.ActiveNormalSlopes
public import Unfoldings.Cap.ClippedCapCoordinates
public import Unfoldings.Cap.DegenerateNormalCurvature

/-! Clip curvature inside the original footprint is supported only on original cap vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance originalCurvatureIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Every actual incident normal comes from an original support plane active at that same point. -/
theorem incidentSlopes_subset_activeSlopes
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (v : T.pairedComplex.Vertex Set.univ) :
    (T.normalizedCap conforming lower).incidentSlopes v ⊆
      K.activeSlopes ((T.normalizedCap conforming lower).projectedVertex v) := by
  let Q := T.normalizedCap conforming lower
  rintro z ⟨i, k, at_vertex, slope_eq⟩
  have corner : (T.projectedTriangle i).vertex k = Q.projectedVertex v :=
    (T.normalizedCap_projectedTriangle_vertex conforming lower i k).symm.trans
      ((Q.projectedVertex_ofCorner i k).symm.trans (congrArg Q.projectedVertex at_vertex))
  have member : Q.projectedVertex v ∈ (T.projectedTriangle i).carrier :=
    corner ▸ (T.projectedTriangle i).vertex_mem k
  exact ⟨T.face i, (T.active i _ member).symm,
    (T.normalizedCap_normalSlope conforming lower i).symm.trans slope_eq⟩

/-- A regular point of any original face remains intrinsically flat in the actual extension. -/
theorem interiorCurvature_eq_zero_at_regular_original
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    (v : T.pairedComplex.Vertex Set.univ) (f : Face)
    (member : (T.normalizedCap conforming lower).projectedVertex v ∈
      (K.projectedTriangle f).carrier)
    (regular : ¬ (K.projectedTriangle f).IsVertex
      ((T.normalizedCap conforming lower).projectedVertex v)) :
    T.pairedComplex.interiorAngularDefect Set.univ v = 0 := by
  apply (T.normalizedCap conforming lower).interiorCurvature_eq_zero_of_incidentSlopes_collinear
    (fun i => height (T.face i)) v
  exact Collinear.subset (T.incidentSlopes_subset_activeSlopes conforming lower v)
    (K.activeSlopes_collinear_of_nonvertex f member regular)

/-- Inside the original cap, extension and subdivision create no new positive-curvature vertices. -/
theorem exists_original_corner_of_positive_curvature
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2)
    (v : T.pairedComplex.Vertex Set.univ)
    (member : (T.normalizedCap conforming lower).projectedVertex v ∈ K.footprint)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    ∃ f i, (K.projectedTriangle f).vertex i =
      (T.normalizedCap conforming lower).projectedVertex v := by
  obtain ⟨f, inside⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset member)
  by_cases vertex : (K.projectedTriangle f).IsVertex
      ((T.normalizedCap conforming lower).projectedVertex v)
  · obtain ⟨i, equal⟩ := vertex
    exact ⟨f, i, equal⟩
  · exact (curved.ne' (T.interiorCurvature_eq_zero_at_regular_original conforming lower height
      v f inside vertex)).elim

end Unfoldings.ConvexCap.ClipSpatialTriangles
