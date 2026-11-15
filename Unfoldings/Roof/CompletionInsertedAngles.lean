module

public import Unfoldings.Roof.CompletionSubdivisionAngles
public import Unfoldings.Roof.CompletionFaceStraightAngles
public import Unfoldings.Complex.SubdivisionInteriors
public import Unfoldings.Boundary.Exact

/-! Refinement vertices in old faces and open cut banks have their exact flat fan angles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionInsertedAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Geometric angle contributions with one named parent are precisely those of its face patch. -/
theorem original_corner_angle_sum_at_point (f : Face) (p : Plane) :
    (∑ d : E.originalComplex.Corner, if E.originalParent d.1 = f ∧
      E.originalSubdivision.place d.1 ((E.originalComplex.triangle d.1).vertex d.2) = p
      then (E.originalComplex.triangle d.1).cornerAngle d.2 else 0) =
    ∑ c : (E.facePieceComplex f).Corner, if (E.facePieceDevelopment f).place c.1
      (((E.facePieceComplex f).triangle c.1).vertex c.2) = p
      then ((E.facePieceComplex f).triangle c.1).cornerAngle c.2 else 0 := by
  classical
  let weight (d : E.originalComplex.Corner) : ℝ :=
    if E.originalSubdivision.place d.1 ((E.originalComplex.triangle d.1).vertex d.2) = p
    then (E.originalComplex.triangle d.1).cornerAngle d.2 else 0
  calc
    _ = ∑ d : E.originalComplex.Corner, if E.originalParent d.1 = f then weight d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases parent : E.originalParent d.1 = f <;> simp [weight, parent]
    _ = ∑ d : {d : E.originalComplex.Corner // E.originalParent d.1 = f}, weight d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ c : (E.facePieceComplex f).Corner, weight (E.facePieceCornerEquiv f c).val :=
      (Equiv.sum_comp (E.facePieceCornerEquiv f) (fun d => weight d.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      have parent := E.originalParent_eq (⟨c.1.val, f, c.1.property⟩ : E.originalPieceSet)
        c.1.property
      change (if E.originalCoordinates c.1.val
          (E.originalParent ⟨c.1.val, f, c.1.property⟩)
          ((E.partition.triangle c.1.val).vertex c.2) = p
        then (E.partition.triangle c.1.val).cornerAngle c.2 else 0) =
        (if E.originalCoordinates c.1.val f ((E.partition.triangle c.1.val).vertex c.2) = p
        then (E.partition.triangle c.1.val).cornerAngle c.2 else 0)
      rw [parent]

open Classical in
/-- The actual patch's injectivity identifies its geometric corner sum with its true fan. -/
theorem facePiece_corner_angle_sum_at_vertex (f : Face)
    (w : (E.facePieceComplex f).Vertex Set.univ) :
    (∑ c : (E.facePieceComplex f).Corner, if (E.facePieceDevelopment f).place c.1
      (((E.facePieceComplex f).triangle c.1).vertex c.2) =
        (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w)
      then ((E.facePieceComplex f).triangle c.1).cornerAngle c.2 else 0) =
        (E.facePieceComplex f).totalAngle Set.univ w := by
  classical
  apply Finset.sum_congr rfl
  intro c _
  have same : (E.facePieceDevelopment f).place c.1
      (((E.facePieceComplex f).triangle c.1).vertex c.2) =
        (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w) ↔
      (E.facePieceComplex f).vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      exact (E.facePieceComplex f).vertexPoint_injective Set.univ
        (E.facePieceDevelopment_injective f equal)
    · rintro rfl
      rfl
  by_cases matched : (E.facePieceComplex f).vertexOfCorner Set.univ c = w
  · simp only [(same.mpr matched), matched, ite_true]
  · simp only [mt same.mp matched, matched, ite_false]

open Classical in
/-- A cut point with only one old tagged representative has exactly its actual face-patch fan. -/
theorem original_totalAngle_of_single_representative (retain : Set C.Seam) (f : Face)
    (x : C.Cell f) (fine : E.originalComplex.Vertex (E.originalRetain retain))
    (at_point : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) = C.faceMap retain f x)
    (isolated : ∀ b : C.Total, MetricGluing.point C.Cell (C.glue retain) b =
      C.faceMap retain f x → b = ⟨f, x⟩) :
    ∃ w : (E.facePieceComplex f).Vertex Set.univ,
      (E.facePieceDevelopment f).toPlane ((E.facePieceComplex f).vertexPoint Set.univ w) = x.val ∧
      E.originalComplex.totalAngle (E.originalRetain retain) fine =
        (E.facePieceComplex f).totalAngle Set.univ w := by
  classical
  let S := E.originalSubdivision
  let H := E.originalSubdivision_conforming retain
  have same (d : E.originalComplex.Corner) :
      E.originalComplex.vertexOfCorner (E.originalRetain retain) d = fine ↔
        S.parentPoint (E.originalComplex.cornerPoint d) = ⟨f, x⟩ := by
    constructor
    · intro equal
      apply isolated
      exact (congrArg (fun w => H.metricEquiv
        (E.originalComplex.vertexPoint (E.originalRetain retain) w)) equal).trans at_point
    · intro equal
      apply E.originalComplex.vertexPoint_injective (E.originalRetain retain)
      apply H.metricEquiv.injective
      exact (congrArg (MetricGluing.point C.Cell (C.glue retain)) equal).trans at_point.symm
  obtain ⟨d, rfl⟩ := E.originalComplex.vertexOfCorner_surjective (E.originalRetain retain) fine
  have tagged := (same d).mp rfl
  have parent : E.originalParent d.1 = f := congrArg Sigma.fst tagged
  have coordinates : S.place d.1 ((E.originalComplex.triangle d.1).vertex d.2) = x.val :=
    congrArg (fun a : C.Total => a.2.val) tagged
  let j : E.facePieceSet f := ⟨d.1.val, by
    have contained := E.originalParent_contains d.1
    rwa [parent] at contained⟩
  let w := (E.facePieceComplex f).vertexOfCorner Set.univ (j, d.2)
  have apex : (E.facePieceDevelopment f).toPlane
      ((E.facePieceComplex f).vertexPoint Set.univ w) = x.val := by
    change E.originalCoordinates d.1.val f ((E.partition.triangle d.1.val).vertex d.2) = _
    change E.originalCoordinates d.1.val (E.originalParent d.1)
      ((E.partition.triangle d.1.val).vertex d.2) = _ at coordinates
    rwa [parent] at coordinates
  refine ⟨w, apex, ?_⟩
  calc
    _ = ∑ c : E.originalComplex.Corner, if E.originalParent c.1 = f ∧
        S.place c.1 ((E.originalComplex.triangle c.1).vertex c.2) = x.val
        then (E.originalComplex.triangle c.1).cornerAngle c.2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      have condition : E.originalComplex.vertexOfCorner (E.originalRetain retain) c =
          E.originalComplex.vertexOfCorner (E.originalRetain retain) d ↔
          E.originalParent c.1 = f ∧
            S.place c.1 ((E.originalComplex.triangle c.1).vertex c.2) = x.val := by
        rw [same c]
        constructor
        · intro equal
          exact ⟨congrArg Sigma.fst equal, congrArg (fun a : C.Total => a.2.val) equal⟩
        · rintro ⟨face, point⟩
          exact S.parentPoint_eq face point
      by_cases matched : E.originalComplex.vertexOfCorner (E.originalRetain retain) c =
          E.originalComplex.vertexOfCorner (E.originalRetain retain) d
      · simp only [matched, condition.mp matched, and_self, ite_true]
      · simp only [matched, mt condition.mpr matched, ite_false]
    _ = _ := by
      rw [E.original_corner_angle_sum_at_point f x.val, ← apex]
      exact E.facePiece_corner_angle_sum_at_vertex f w

open Classical in
/-- New vertices strictly inside old faces remain exactly flat for every original cut set. -/
theorem original_totalAngle_at_face_interior (retain : Set C.Seam) (f : Face)
    (x : C.Cell f) (inside : x.val ∈ interior (C.triangle f).carrier)
    (fine : E.originalComplex.Vertex (E.originalRetain retain))
    (at_point : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) = C.faceMap retain f x) :
    E.originalComplex.totalAngle (E.originalRetain retain) fine = 2 * Real.pi := by
  have isolated (b : C.Total) (equal : MetricGluing.point C.Cell (C.glue retain) b =
      C.faceMap retain f x) : b = ⟨f, x⟩ := by
    have related : Relation.EqvGen (C.glue retain) (⟨f, x⟩ : C.Total) b :=
      (C.point_eq_iff retain _ _).mp equal.symm
    exact (C.eq_of_related_interior (a := ⟨f, x⟩) inside related).symm
  obtain ⟨w, apex, angle⟩ := E.original_totalAngle_of_single_representative retain f x fine
    at_point isolated
  exact angle.trans (E.facePiece_totalAngle_at_original_interior f w (apex.symm ▸ inside))

open Classical in
/-- New vertices along the open part of an actual old cut bank have exactly straight fan angle. -/
theorem original_totalAngle_at_bank_interior (retain : Set C.Seam)
    (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ C.IsVertex (C.edgePoint bank.val x))
    (fine : E.originalComplex.Vertex (E.originalRetain retain))
    (at_point : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) = C.bankMap retain bank x) :
    E.originalComplex.totalAngle (E.originalRetain retain) fine = Real.pi := by
  obtain ⟨w, apex, angle⟩ := E.original_totalAngle_of_single_representative retain bank.val.face
    ((C.triangle bank.val.face).edgeMap bank.val.edge x) fine at_point (fun b equal =>
      ((C.point_eq_iff_of_boundary bank.property regular (C.edgePoint_onEdge bank.val x)).mp
        equal.symm).symm)
  exact angle.trans (E.facePiece_totalAngle_at_noncorner_boundary bank.val.face w
    (apex.symm ▸ (C.triangle bank.val.face).edge_subset_frontier bank.val.edge x.property)
    (apex.symm ▸ regular))

open Classical in
/-- Refinement of an original bank introduces no extra real exterior rolling turn. -/
theorem original_bank_inserted_turn_eq_zero (retain : Set C.Seam)
    (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ C.IsVertex (C.edgePoint bank.val x))
    (fine : E.originalComplex.Vertex (E.originalRetain retain))
    (at_point : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) = C.bankMap retain bank x) :
    Real.pi - E.originalComplex.totalAngle (E.originalRetain retain) fine = 0 := by
  rw [E.original_totalAngle_at_bank_interior retain bank x regular fine at_point, sub_self]

end Unfoldings.ConvexRoof.CompletionMesh
