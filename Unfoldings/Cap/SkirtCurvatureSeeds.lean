module

public import Unfoldings.Cap.SkirtRadialCuts
public import Unfoldings.Cap.LineRefinementCurvature
public import Unfoldings.Cap.OriginalCurvatureSupport

/-!
# Finite skirt seeds selected before continuation meshing

Use corners of the preceding physical partition outside the original cap's
interior, together with original rim corners. After meshing their radial tails,
every positive-curvature vertex is an original cap vertex or lies on a selected
tail component. No post-meshing positive-curvature certificate is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

def skirtSeedSet : Set Plane :=
  (Set.range (fun a : T.Index × Fin 3 => (T.projectedTriangle a.1).vertex a.2) ∪
    Set.range (fun a : Face × Fin 3 => (K.projectedTriangle a.1).vertex a.2)) \ interior K.footprint

theorem finite_skirtSeedSet : T.skirtSeedSet.Finite := by
  let := T.finite
  exact ((Set.finite_range _).union (Set.finite_range _)).subset Set.sdiff_subset

theorem skirtSeedSet_subset_clip (lower : Z < 0) : T.skirtSeedSet ⊆ K.clipFootprint Z := by
  rintro p ⟨(⟨⟨i, k⟩, rfl⟩ | ⟨⟨f, k⟩, rfl⟩), _outside⟩
  · exact T.cover.symm.subset (Set.mem_iUnion.mpr ⟨i, (T.projectedTriangle i).vertex_mem k⟩)
  · exact (K.projectedTriangle_subset_clippedSupportCell lower.le f
      ((K.projectedTriangle f).vertex_mem k)).1

/-- Select the actual finite seed family before performing any continuation meshing. -/
def cornerTails {q : Plane} (origin : q ∈ interior K.footprint) (positive : 0 < K.roofHeight q)
    (lower : Z < 0) : K.SkirtTailFamily Z q := by
  let := T.finite_skirtSeedSet.to_subtype
  exact K.skirtTailFamily origin positive lower (fun p : T.skirtSeedSet => p.val)
    (fun p => T.skirtSeedSet_subset_clip lower p.property) (fun p => p.property.2)

theorem cornerTails_original_rim_corner {q : Plane} (origin : q ∈ interior K.footprint)
    (positive : 0 < K.roofHeight q) (lower : Z < 0) (f : Face) (k : Fin 3)
    (rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint) :
    (K.projectedTriangle f).vertex k ∈
      ⋃ c : (T.cornerTails origin positive lower).Component,
        ((T.cornerTails origin positive lower).componentTail c).carrier := by
  have member : (K.projectedTriangle f).vertex k ∈ T.skirtSeedSet :=
    ⟨Or.inr ⟨(f, k), rfl⟩, rim⟩
  exact (T.cornerTails origin positive lower).seeds_covered ⟨_, member⟩

/-- Meshed positive curvature lies on original vertices or constructed skirt cuts. -/
theorem cornerMesh_curvature_covered {q : Plane} (origin : q ∈ interior K.footprint)
    (positive : 0 < K.roofHeight q) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let F := T.cornerTails origin positive lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ v : L.partition.pairedComplex.Vertex Set.univ,
      0 < L.partition.pairedComplex.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ Set.range K.projectedVertex ∨
          Q.projectedVertex v ∈ ⋃ c : F.Component, (F.componentTail c).carrier := by
  let F := T.cornerTails origin positive lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  refine fun v curved => ?_
  by_cases inside : Q.projectedVertex v ∈ K.footprint
  · obtain ⟨f, k, at_corner⟩ := L.partition.exists_original_corner_of_positive_curvature
      L.conforming lower height v inside curved
    exact Or.inl ⟨C.vertexOfCorner Set.univ (f, k), at_corner⟩
  · have supported := T.alignToLines_curvature_support
      (K.originalAndSegmentEquations F.first F.last F.different)
      (K.originalAndSegmentEquations_ne_zero F.first F.last F.different)
      conforming lower height v curved
    obtain ⟨i, k, at_corner⟩ := supported
    have member : Q.projectedVertex v ∈ T.skirtSeedSet := by
      refine ⟨Or.inl ⟨(i, k), at_corner⟩, fun interior_point => inside ?_⟩
      exact interior_subset interior_point
    exact Or.inr (F.seeds_covered ⟨_, member⟩)

end Unfoldings.ConvexCap.ClipSpatialTriangles
