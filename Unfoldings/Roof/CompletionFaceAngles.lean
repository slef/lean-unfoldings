module

public import Unfoldings.Roof.CompletionFacePatch
public import Unfoldings.Development.FlatCap
public import Unfoldings.Cap.TriangularFootprintAngles
public import Unfoldings.Geometry.TriangleSubsetCorners

/-! Original corner angles are preserved exactly by their physical completion pieces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionFaceAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The actual pieces in one old face form a flat cap in that face's original metric coordinates. -/
def facePieceFlatCap : ConvexCap (E.facePieceComplex f) :=
  (E.facePieceDevelopment f).flatCap (E.facePieceDevelopment_injective f)
    (by rw [E.facePieceDevelopment_range f]; exact (C.triangle f).convex_carrier)
    (by rw [E.facePieceDevelopment_range f]; exact (C.triangle f).interior_nonempty)

open Classical in
theorem facePieceFlatCap_footprint : (E.facePieceFlatCap f).footprint = (C.triangle f).carrier :=
  ((E.facePieceDevelopment f).flatCap_footprint _ _ _).trans (E.facePieceDevelopment_range f)

open Classical in
/-- The actual selected fine corners at an old corner sum to exactly its old Euclidean angle. -/
theorem facePiece_totalAngle_at_original_corner
    (w : (E.facePieceComplex f).Vertex Set.univ) (i : Fin 3)
    (apex : (E.facePieceDevelopment f).toPlane
      ((E.facePieceComplex f).vertexPoint Set.univ w) = (C.triangle f).vertex i) :
    (E.facePieceComplex f).totalAngle Set.univ w = (C.triangle f).cornerAngle i := by
  have projected : (E.facePieceFlatCap f).projectedVertex w = (C.triangle f).vertex i :=
    ((E.facePieceDevelopment f).horizontalFolding_projection _).trans apex
  have corner := (E.facePieceFlatCap f).projectedTotalAngle_eq_triangle_corner
    (C.triangle f) (E.facePieceFlatCap_footprint f) w i projected
  exact ((E.facePieceDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ w).symm.trans corner

open Classical in
/-- Each original corner has an actual vertex in its physical fine-face patch. -/
theorem exists_facePiece_original_corner (i : Fin 3) :
    ∃ w : (E.facePieceComplex f).Vertex Set.univ,
      (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w) =
        (C.triangle f).vertex i := by
  let R := E.facePieceComplex f
  let D := E.facePieceDevelopment f
  obtain ⟨x, at_corner⟩ := (E.facePieceDevelopment_range f).symm.subset
    ((C.triangle f).vertex_mem i)
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective R.Cell (R.glue Set.univ) x
  have contained : (D.placedTriangle j).carrier ⊆ (C.triangle f).carrier := by
    rw [D.placedTriangle_carrier]
    rintro z ⟨q, hq, rfl⟩
    exact (E.facePieceDevelopment_range f).subset ⟨R.faceMap Set.univ j ⟨q, hq⟩, rfl⟩
  have member : (C.triangle f).vertex i ∈ (D.placedTriangle j).carrier := by
    rw [D.placedTriangle_carrier]
    exact ⟨y.val, y.property, at_corner⟩
  obtain ⟨k, equal⟩ := (D.placedTriangle j).isVertex_of_contained_corner (C.triangle f)
    contained i member
  exact ⟨R.vertexOfCorner Set.univ (j, k), equal⟩

open Classical in
/-- Geometrically grouped fine-corner angles add to the old corner angle exactly. -/
theorem facePiece_sum_cornerAngles (i : Fin 3) :
    (∑ c : (E.facePieceComplex f).Corner,
      if (E.facePieceDevelopment f).place c.1
          (((E.facePieceComplex f).triangle c.1).vertex c.2) = (C.triangle f).vertex i
      then ((E.facePieceComplex f).triangle c.1).cornerAngle c.2 else 0) =
        (C.triangle f).cornerAngle i := by
  classical
  let R := E.facePieceComplex f
  let D := E.facePieceDevelopment f
  obtain ⟨w, at_corner⟩ := E.exists_facePiece_original_corner f i
  have corner := E.facePiece_totalAngle_at_original_corner f w i at_corner
  have same (c : R.Corner) : D.place c.1 ((R.triangle c.1).vertex c.2) =
      (C.triangle f).vertex i ↔ R.vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      apply R.vertexPoint_injective Set.univ
      apply E.facePieceDevelopment_injective f
      exact equal.trans at_corner.symm
    · intro equal
      exact (congrArg (fun v => D.toPlane (R.vertexPoint Set.univ v)) equal).trans at_corner
  calc
    _ = R.totalAngle Set.univ w := by
      unfold TriangleComplex.totalAngle
      apply Finset.sum_congr rfl
      intro c _
      change (if D.place c.1 ((R.triangle c.1).vertex c.2) = (C.triangle f).vertex i
        then (R.triangle c.1).cornerAngle c.2 else 0) = _
      by_cases member : R.vertexOfCorner Set.univ c = w
      · simp only [(same c).mpr member, member, ite_true]
      · simp only [mt (same c).mp member, member, ite_false]
    _ = _ := corner

end Unfoldings.ConvexRoof.CompletionMesh
