module

public import Unfoldings.Cap.ClippedCapCoordinates
public import Unfoldings.Cap.ConstrainedClipParents
public import Unfoldings.Cap.RefinementCurvatureSupport

/-! Actual line meshing creates no curvature away from the preceding physical roof corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- Every positive-curvature vertex after arbitrary line meshing lies at a pre-meshing corner. -/
theorem alignToLines_curvature_support {J : Type} [Finite J]
    (equation : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, equation j ≠ 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let L := T.alignToLines equation proper lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ v : L.partition.pairedComplex.Vertex Set.univ,
      0 < L.partition.pairedComplex.interiorAngularDefect Set.univ v →
        ∃ i j, (T.projectedTriangle i).vertex j = Q.projectedVertex v := by
  let L := T.alignToLines equation proper lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  obtain ⟨parent, subordinate⟩ := T.alignToLines_subordinate equation proper lower
  have inside (i : L.partition.Index) :
      (Q.projectedTriangle i).carrier ⊆ (T.projectedTriangle (parent i)).carrier := by
    rw [L.partition.normalizedCap_projectedTriangle_carrier L.conforming lower]
    exact (subordinate i).1
  have normal_eq (i : L.partition.Index) :
      Q.normalSlope i = K.normalSlope (T.face (parent i)) := by
    rw [L.partition.normalizedCap_normalSlope L.conforming lower, (subordinate i).2]
  exact fun v curved => Q.exists_parent_corner_of_positive_curvature T.projectedTriangle
    conforming T.separated (fun i => K.normalSlope (T.face i)) parent inside normal_eq
      (fun i => height (L.partition.face i)) v curved

end Unfoldings.ConvexCap.ClipSpatialTriangles
