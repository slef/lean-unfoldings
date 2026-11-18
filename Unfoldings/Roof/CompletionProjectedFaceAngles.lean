module

public import Unfoldings.Development.AffineProjectionEmbedding
public import Unfoldings.Roof.CompletionProjectedFacePatch
public import Unfoldings.Development.FlatCap
public import Unfoldings.Cap.TriangularFootprintAngles
public import Unfoldings.Geometry.TriangleSubsetCorners

/-! Projected corner angles are preserved exactly by their physical completion pieces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionProjectedFaceAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The actual pieces in one old face form a flat cap in that face's projected metric
  coordinates. -/
def facePieceProjectedFlatCap : ConvexCap (E.facePieceProjectedComplex f) :=
  (E.facePieceProjectedDevelopment f).flatCap (E.facePieceProjectedDevelopment_injective f)
    (by rw [E.facePieceProjectedDevelopment_range f]; exact (K.projectedTriangle f).convex_carrier)
    (by rw [E.facePieceProjectedDevelopment_range f]; exact (K.projectedTriangle
      f).interior_nonempty)

open Classical in
theorem facePieceProjectedFlatCap_footprint : (E.facePieceProjectedFlatCap f).footprint =
  (K.projectedTriangle f).carrier :=
  ((E.facePieceProjectedDevelopment f).flatCap_footprint _ _ _).trans
    (E.facePieceProjectedDevelopment_range f)

open Classical in
/-- The actual selected fine corners at an old corner sum to exactly its old Euclidean angle. -/
theorem facePieceProjected_totalAngle_at_original_corner
    (w : (E.facePieceProjectedComplex f).Vertex Set.univ) (i : Fin 3)
    (apex : (E.facePieceProjectedDevelopment f).toPlane
      ((E.facePieceProjectedComplex f).vertexPoint Set.univ w) = (K.projectedTriangle f).vertex i) :
    (E.facePieceProjectedComplex f).totalAngle Set.univ w = (K.projectedTriangle
      f).cornerAngle i := by
  have projected : (E.facePieceProjectedFlatCap f).projectedVertex w = (K.projectedTriangle
    f).vertex i :=
    ((E.facePieceProjectedDevelopment f).horizontalFolding_projection _).trans apex
  have corner := (E.facePieceProjectedFlatCap f).projectedTotalAngle_eq_triangle_corner
    (K.projectedTriangle f) (E.facePieceProjectedFlatCap_footprint f) w i projected
  exact ((E.facePieceProjectedDevelopment f).flatCap_projectedTotalAngle _ _ _ Set.univ
    w).symm.trans corner

open Classical in
/-- Each original corner has an actual vertex in its physical fine-face patch. -/
theorem exists_facePieceProjected_original_corner (i : Fin 3) :
    ∃ w : (E.facePieceProjectedComplex f).Vertex Set.univ,
      (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex f).vertexPoint
        Set.univ w) =
        (K.projectedTriangle f).vertex i := by
  let R := E.facePieceProjectedComplex f
  let D := E.facePieceProjectedDevelopment f
  obtain ⟨x, at_corner⟩ := (E.facePieceProjectedDevelopment_range f).symm.subset
    ((K.projectedTriangle f).vertex_mem i)
  obtain ⟨⟨j, y⟩, rfl⟩ := MetricGluing.point_surjective R.Cell (R.glue Set.univ) x
  have contained : (D.placedTriangle j).carrier ⊆ (K.projectedTriangle f).carrier := by
    rw [D.placedTriangle_carrier]
    rintro z ⟨q, hq, rfl⟩
    exact (E.facePieceProjectedDevelopment_range f).subset ⟨R.faceMap Set.univ j ⟨q, hq⟩, rfl⟩
  have member : (K.projectedTriangle f).vertex i ∈ (D.placedTriangle j).carrier := by
    rw [D.placedTriangle_carrier]
    exact ⟨y.val, y.property, at_corner⟩
  obtain ⟨k, equal⟩ := (D.placedTriangle j).isVertex_of_contained_corner (K.projectedTriangle f)
    contained i member
  exact ⟨R.vertexOfCorner Set.univ (j, k), equal⟩

open Classical in
/-- Geometrically grouped fine-corner angles add to the old corner angle exactly. -/
theorem facePieceProjected_sum_cornerAngles (i : Fin 3) :
    (∑ c : (E.facePieceProjectedComplex f).Corner,
      if (E.facePieceProjectedDevelopment f).place c.1
          (((E.facePieceProjectedComplex f).triangle c.1).vertex c.2) = (K.projectedTriangle
            f).vertex i
      then ((E.facePieceProjectedComplex f).triangle c.1).cornerAngle c.2 else 0) =
        (K.projectedTriangle f).cornerAngle i := by
  classical
  let R := E.facePieceProjectedComplex f
  let D := E.facePieceProjectedDevelopment f
  obtain ⟨w, at_corner⟩ := E.exists_facePieceProjected_original_corner f i
  have corner := E.facePieceProjected_totalAngle_at_original_corner f w i at_corner
  have same (c : R.Corner) : D.place c.1 ((R.triangle c.1).vertex c.2) =
      (K.projectedTriangle f).vertex i ↔ R.vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      apply R.vertexPoint_injective Set.univ
      apply E.facePieceProjectedDevelopment_injective f
      exact equal.trans at_corner.symm
    · intro equal
      exact (congrArg (fun v => D.toPlane (R.vertexPoint Set.univ v)) equal).trans at_corner
  calc
    _ = R.totalAngle Set.univ w := by
      unfold TriangleComplex.totalAngle
      apply Finset.sum_congr rfl
      intro c _
      change (if D.place c.1 ((R.triangle c.1).vertex c.2) = (K.projectedTriangle f).vertex i
        then (R.triangle c.1).cornerAngle c.2 else 0) = _
      by_cases member : R.vertexOfCorner Set.univ c = w
      · simp only [(same c).mpr member, member, ite_true]
      · simp only [mt (same c).mp member, member, ite_false]
    _ = _ := corner

end Unfoldings.ConvexRoof.CompletionMesh
