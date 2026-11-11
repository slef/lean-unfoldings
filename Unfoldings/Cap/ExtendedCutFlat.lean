module

public import Unfoldings.Cap.ExtendedCutMesh
public import Unfoldings.Cap.ProjectedSeamEndpoints
public import Unfoldings.Cap.CurvatureCutDevelopment

/-! The actual constructed extended retained-seam set has flat intrinsic interior vertex copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Every positive-curvature vertex is an endpoint of an actual removed seam. -/
theorem extended_cut_curvature_endpoints (T : K.ClipSpatialTriangles Z)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (positive : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside positive lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ v : L.partition.pairedComplex.Vertex Set.univ,
      0 < L.partition.pairedComplex.interiorAngularDefect Set.univ v →
        ∃ s b, s ∉ M.extendedRetain T F lower ∧ v = L.partition.pairedComplex.seamVertex s b := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside positive lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun v curved => ?_
  have internal_v : ¬ L.partition.pairedComplex.IsBoundaryVertex Set.univ v := by
    intro boundary
    have zero : L.partition.pairedComplex.interiorAngularDefect Set.univ v = 0 := by
      simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
    exact curved.ne' zero
  have inside_clip : Q.projectedVertex v ∈ interior (K.clipFootprint Z) := by
    have member := (Q.projectedVertex_mem_interior_iff v).mpr internal_v
    rw [L.partition.normalizedCap_footprint L.conforming lower] at member
    exact member
  have member : Q.projectedVertex v ∈ M.extendedGeometricCuts F :=
    M.extended_cut_curvature_covered T internal positive lower conforming height v curved
  obtain ⟨s, cut, on_edge⟩ := M.extended_cut_seam T F lower member inside_clip
  have projected_edge : Q.projectedVertex v ∈
      (Q.projectedTriangle (L.partition.pairedComplex.left s).face).edge
        (L.partition.pairedComplex.left s).edge :=
    (L.partition.normalizedCap_projectedTriangle_edge L.conforming lower _ _).symm.subset on_edge
  obtain ⟨b, endpoint⟩ := Q.vertex_eq_seamEndpoint_of_projected_edge v s projected_edge
  exact ⟨s, b, cut, endpoint⟩

/-- Flat auxiliary vertices may remain uncut; interior cut copies still have angle two pi. -/
theorem extended_cut_interior_flat (T : K.ClipSpatialTriangles Z)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (positive : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside positive lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ w : L.partition.pairedComplex.Vertex (M.extendedRetain T F lower),
      ¬ L.partition.pairedComplex.IsBoundaryVertex (M.extendedRetain T F lower) w →
        L.partition.pairedComplex.totalAngle (M.extendedRetain T F lower) w = 2 * Real.pi := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside positive lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  exact Q.interior_flat_of_curvature_cut (M.extendedRetain T F lower)
    (M.extended_cut_curvature_endpoints T internal positive lower conforming height)

end Unfoldings.ConvexCap.SectorForest
