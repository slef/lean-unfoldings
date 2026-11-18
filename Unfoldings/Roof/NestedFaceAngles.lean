module

public import Unfoldings.Roof.NestedFacePatch
public import Unfoldings.Development.FlatCap
public import Unfoldings.Cap.TriangularFootprintAngles
public import Unfoldings.Geometry.TriangleSubsetCorners

/-! Complete nested face patches conserve each old Euclidean corner angle exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)
  (conforming : TriangleFamily.Conforming U.projectedTriangle)
  (inside : (interior (clip family W)).Nonempty) (cover : T.FaceRefinement U)

local instance nestedFaceAnglesOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedFaceAnglesNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

open Classical in
/-- Each original metric face is the footprint of its actual flat fine-face patch. -/
def nestedFaceFlatCap (f : T.Index) : ConvexCap (T.nestedFaceComplex U f) :=
  (T.nestedFaceDevelopment U f).flatCap
    (T.nestedFaceDevelopment_injective U conforming inside cover f)
    (by rw [T.nestedFaceDevelopment_range U cover f]; exact (T.triangle f).convex_carrier)
    (by rw [T.nestedFaceDevelopment_range U cover f]; exact (T.triangle f).interior_nonempty)

open Classical in
theorem nestedFaceFlatCap_footprint (f : T.Index) :
    (T.nestedFaceFlatCap U conforming inside cover f).footprint = (T.triangle f).carrier :=
  ((T.nestedFaceDevelopment U f).flatCap_footprint _ _ _).trans
    (T.nestedFaceDevelopment_range U cover f)

include conforming inside cover in
open Classical in
theorem nestedFace_totalAngle_at_old_corner (f : T.Index)
    (w : (T.nestedFaceComplex U f).Vertex Set.univ) (i : Fin 3)
    (apex : (T.nestedFaceDevelopment U f).toPlane
      ((T.nestedFaceComplex U f).vertexPoint Set.univ w) = (T.triangle f).vertex i) :
    (T.nestedFaceComplex U f).totalAngle Set.univ w = (T.triangle f).cornerAngle i := by
  have projected : (T.nestedFaceFlatCap U conforming inside cover f).projectedVertex w =
      (T.triangle f).vertex i :=
    ((T.nestedFaceDevelopment U f).horizontalFolding_projection _).trans apex
  have corner :=
    (T.nestedFaceFlatCap U conforming inside cover f).projectedTotalAngle_eq_triangle_corner
      (T.triangle f) (T.nestedFaceFlatCap_footprint U conforming inside cover f) w i projected
  exact ((T.nestedFaceDevelopment U f).flatCap_projectedTotalAngle _ _ _ Set.univ w).symm.trans
    corner

include cover in
open Classical in
theorem exists_nestedFace_old_corner (f : T.Index) (i : Fin 3) :
    ∃ w : (T.nestedFaceComplex U f).Vertex Set.univ,
      (T.nestedFaceDevelopment U f).toPlane ((T.nestedFaceComplex U f).vertexPoint Set.univ w) =
        (T.triangle f).vertex i := by
  let R := T.nestedFaceComplex U f
  let D := T.nestedFaceDevelopment U f
  obtain ⟨x, at_corner⟩ := (T.nestedFaceDevelopment_range U cover f).symm.subset
    ((T.triangle f).vertex_mem i)
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective R.Cell (R.glue Set.univ) x
  have contained : (D.placedTriangle j).carrier ⊆ (T.triangle f).carrier := by
    rw [D.placedTriangle_carrier]
    rintro z ⟨q, hq, rfl⟩
    exact (T.nestedFaceDevelopment_range U cover f).subset ⟨R.faceMap Set.univ j ⟨q, hq⟩, rfl⟩
  have member : (T.triangle f).vertex i ∈ (D.placedTriangle j).carrier := by
    rw [D.placedTriangle_carrier]
    exact ⟨y.val, y.property, at_corner⟩
  obtain ⟨k, equal⟩ := (D.placedTriangle j).isVertex_of_contained_corner (T.triangle f)
    contained i member
  exact ⟨R.vertexOfCorner Set.univ (j, k), equal⟩

include conforming inside cover in
open Classical in
/-- Geometric corner grouping gives exact angle sums, independently of any retained cuts. -/
theorem nestedFace_sum_cornerAngles (f : T.Index) (i : Fin 3) :
    (∑ c : (T.nestedFaceComplex U f).Corner,
      if (T.nestedFaceDevelopment U f).place c.1
          (((T.nestedFaceComplex U f).triangle c.1).vertex c.2) = (T.triangle f).vertex i
      then ((T.nestedFaceComplex U f).triangle c.1).cornerAngle c.2 else 0) =
        (T.triangle f).cornerAngle i := by
  classical
  let R := T.nestedFaceComplex U f
  let D := T.nestedFaceDevelopment U f
  obtain ⟨w, at_corner⟩ := T.exists_nestedFace_old_corner U cover f i
  have corner := T.nestedFace_totalAngle_at_old_corner U conforming inside cover f w i at_corner
  have same (c : R.Corner) : D.place c.1 ((R.triangle c.1).vertex c.2) =
      (T.triangle f).vertex i ↔ R.vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      apply R.vertexPoint_injective Set.univ
      apply T.nestedFaceDevelopment_injective U conforming inside cover f
      exact equal.trans at_corner.symm
    · intro equal
      exact (congrArg (fun v => D.toPlane (R.vertexPoint Set.univ v)) equal).trans at_corner
  calc
    _ = R.totalAngle Set.univ w := by
      unfold TriangleComplex.totalAngle
      apply Finset.sum_congr rfl
      intro c _
      change (if D.place c.1 ((R.triangle c.1).vertex c.2) = (T.triangle f).vertex i
        then (R.triangle c.1).cornerAngle c.2 else 0) = _
      by_cases member : R.vertexOfCorner Set.univ c = w
      · simp only [(same c).mpr member, member, ite_true]
      · simp only [mt (same c).mp member, member, ite_false]
    _ = _ := corner

end Unfoldings.SpatialEnvelope.Triangulation
