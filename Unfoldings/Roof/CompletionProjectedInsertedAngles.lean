module

public import Unfoldings.Roof.CompletionProjectedSubdivisionAngles
public import Unfoldings.Roof.CompletionProjectedFaceStraightAngles
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

local instance completionProjectedInsertedAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Geometric angle contributions with one named parent are precisely those of its face patch. -/
theorem original_projected_corner_angle_sum_at_point (f : Face) (p : Plane) :
    (∑ d : E.originalProjectedComplex.Corner, if E.originalParent d.1 = f ∧
      E.originalProjectedSubdivision.place d.1 ((E.originalProjectedComplex.triangle
        d.1).vertex d.2) = p
      then (E.originalProjectedComplex.triangle d.1).cornerAngle d.2 else 0) =
    ∑ c : (E.facePieceProjectedComplex f).Corner, if (E.facePieceProjectedDevelopment f).place c.1
      (((E.facePieceProjectedComplex f).triangle c.1).vertex c.2) = p
      then ((E.facePieceProjectedComplex f).triangle c.1).cornerAngle c.2 else 0 := by
  classical
  let weight (d : E.originalProjectedComplex.Corner) : ℝ :=
    if E.originalProjectedSubdivision.place d.1 ((E.originalProjectedComplex.triangle
      d.1).vertex d.2) = p
    then (E.originalProjectedComplex.triangle d.1).cornerAngle d.2 else 0
  calc
    _ = ∑ d : E.originalProjectedComplex.Corner, if E.originalParent d.1 = f then weight d
      else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases parent : E.originalParent d.1 = f <;> simp [weight, parent]
    _ = ∑ d : {d : E.originalProjectedComplex.Corner // E.originalParent d.1 = f}, weight
      d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ c : (E.facePieceProjectedComplex f).Corner, weight (E.facePieceProjectedCornerEquiv
      f c).val :=
      (Equiv.sum_comp (E.facePieceProjectedCornerEquiv f) (fun d => weight d.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rfl

open Classical in
/-- The actual patch's injectivity identifies its geometric corner sum with its true fan. -/
theorem facePieceProjected_corner_angle_sum_at_vertex (f : Face)
    (w : (E.facePieceProjectedComplex f).Vertex Set.univ) :
    (∑ c : (E.facePieceProjectedComplex f).Corner, if (E.facePieceProjectedDevelopment f).place c.1
      (((E.facePieceProjectedComplex f).triangle c.1).vertex c.2) =
        (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex
          f).vertexPoint Set.univ w)
      then ((E.facePieceProjectedComplex f).triangle c.1).cornerAngle c.2 else 0) =
        (E.facePieceProjectedComplex f).totalAngle Set.univ w := by
  classical
  apply Finset.sum_congr rfl
  intro c _
  have same : (E.facePieceProjectedDevelopment f).place c.1
      (((E.facePieceProjectedComplex f).triangle c.1).vertex c.2) =
        (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex
          f).vertexPoint Set.univ w) ↔
      (E.facePieceProjectedComplex f).vertexOfCorner Set.univ c = w := by
    constructor
    · intro equal
      exact (E.facePieceProjectedComplex f).vertexPoint_injective Set.univ
        (E.facePieceProjectedDevelopment_injective f equal)
    · rintro rfl
      rfl
  by_cases matched : (E.facePieceProjectedComplex f).vertexOfCorner Set.univ c = w
  · simp only [(same.mpr matched), matched, ite_true]
  · simp only [mt same.mp matched, matched, ite_false]

open Classical in
/-- A cut point with only one old tagged representative has exactly its actual face-patch fan. -/
theorem original_projected_totalAngle_of_single_representative (retain : Set
  K.projectedMetricComplex.Seam) (f : Face)
    (x : K.projectedMetricComplex.Cell f) (fine : E.originalProjectedComplex.Vertex
      (E.originalRetain retain))
    (at_point : (E.originalProjectedSubdivision_conforming retain).metricEquiv
      (E.originalProjectedComplex.vertexPoint (E.originalRetain retain) fine) =
        K.projectedMetricComplex.faceMap retain f x)
    (isolated : ∀ b : K.projectedMetricComplex.Total, MetricGluing.point
      K.projectedMetricComplex.Cell (K.projectedMetricComplex.glue retain) b =
      K.projectedMetricComplex.faceMap retain f x → b = ⟨f, x⟩) :
    ∃ w : (E.facePieceProjectedComplex f).Vertex Set.univ,
      (E.facePieceProjectedDevelopment f).toPlane ((E.facePieceProjectedComplex f).vertexPoint
        Set.univ w) = x.val ∧
      E.originalProjectedComplex.totalAngle (E.originalRetain retain) fine =
        (E.facePieceProjectedComplex f).totalAngle Set.univ w := by
  classical
  let S := E.originalProjectedSubdivision
  let H := E.originalProjectedSubdivision_conforming retain
  have same (d : E.originalProjectedComplex.Corner) :
      E.originalProjectedComplex.vertexOfCorner (E.originalRetain retain) d = fine ↔
        S.parentPoint (E.originalProjectedComplex.cornerPoint d) = ⟨f, x⟩ := by
    constructor
    · intro equal
      apply isolated
      exact (congrArg (fun w => H.metricEquiv
        (E.originalProjectedComplex.vertexPoint (E.originalRetain retain) w)) equal).trans at_point
    · intro equal
      apply E.originalProjectedComplex.vertexPoint_injective (E.originalRetain retain)
      apply H.metricEquiv.injective
      exact (congrArg (MetricGluing.point K.projectedMetricComplex.Cell
        (K.projectedMetricComplex.glue retain)) equal).trans at_point.symm
  obtain ⟨d, rfl⟩ := E.originalProjectedComplex.vertexOfCorner_surjective (E.originalRetain
    retain) fine
  have tagged := (same d).mp rfl
  have parent : E.originalParent d.1 = f := congrArg Sigma.fst tagged
  have coordinates : S.place d.1 ((E.originalProjectedComplex.triangle d.1).vertex d.2) = x.val :=
    congrArg (fun a : K.projectedMetricComplex.Total => a.2.val) tagged
  let j : E.facePieceSet f := ⟨d.1.val, by
    have contained := E.originalParent_contains d.1
    rwa [parent] at contained⟩
  let w := (E.facePieceProjectedComplex f).vertexOfCorner Set.univ (j, d.2)
  have apex : (E.facePieceProjectedDevelopment f).toPlane
      ((E.facePieceProjectedComplex f).vertexPoint Set.univ w) = x.val := by
    exact coordinates
  refine ⟨w, apex, ?_⟩
  calc
    _ = ∑ c : E.originalProjectedComplex.Corner, if E.originalParent c.1 = f ∧
        S.place c.1 ((E.originalProjectedComplex.triangle c.1).vertex c.2) = x.val
        then (E.originalProjectedComplex.triangle c.1).cornerAngle c.2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      have condition : E.originalProjectedComplex.vertexOfCorner (E.originalRetain retain) c =
          E.originalProjectedComplex.vertexOfCorner (E.originalRetain retain) d ↔
          E.originalParent c.1 = f ∧
            S.place c.1 ((E.originalProjectedComplex.triangle c.1).vertex c.2) = x.val := by
        rw [same c]
        constructor
        · intro equal
          exact ⟨congrArg Sigma.fst equal, congrArg (fun a : K.projectedMetricComplex.Total =>
            a.2.val) equal⟩
        · rintro ⟨face, point⟩
          exact S.parentPoint_eq face point
      by_cases matched : E.originalProjectedComplex.vertexOfCorner (E.originalRetain retain) c =
          E.originalProjectedComplex.vertexOfCorner (E.originalRetain retain) d
      · simp only [matched, condition.mp matched, and_self, ite_true]
      · simp only [matched, mt condition.mpr matched, ite_false]
    _ = _ := by
      rw [E.original_projected_corner_angle_sum_at_point f x.val, ← apex]
      exact E.facePieceProjected_corner_angle_sum_at_vertex f w

open Classical in
/-- New vertices strictly inside old faces remain exactly flat for every original cut set. -/
theorem original_projected_totalAngle_at_face_interior (retain : Set
  K.projectedMetricComplex.Seam) (f : Face)
    (x : K.projectedMetricComplex.Cell f) (inside : x.val ∈ interior
      (K.projectedMetricComplex.triangle f).carrier)
    (fine : E.originalProjectedComplex.Vertex (E.originalRetain retain))
    (at_point : (E.originalProjectedSubdivision_conforming retain).metricEquiv
      (E.originalProjectedComplex.vertexPoint (E.originalRetain retain) fine) =
        K.projectedMetricComplex.faceMap retain f x) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain) fine = 2 * Real.pi := by
  have isolated (b : K.projectedMetricComplex.Total) (equal : MetricGluing.point
    K.projectedMetricComplex.Cell (K.projectedMetricComplex.glue retain) b =
      K.projectedMetricComplex.faceMap retain f x) : b = ⟨f, x⟩ := by
    have related : Relation.EqvGen (K.projectedMetricComplex.glue retain) (⟨f, x⟩ :
      K.projectedMetricComplex.Total) b :=
      (K.projectedMetricComplex.point_eq_iff retain _ _).mp equal.symm
    exact (K.projectedMetricComplex.eq_of_related_interior (a := ⟨f, x⟩) inside related).symm
  obtain ⟨w, apex, angle⟩ := E.original_projected_totalAngle_of_single_representative retain f
    x fine
    at_point isolated
  exact angle.trans (E.facePieceProjected_totalAngle_at_original_interior f w (apex.symm ▸ inside))

open Classical in
/-- New vertices along the open part of an actual old cut bank have exactly straight fan angle. -/
theorem original_projected_totalAngle_at_bank_interior (retain : Set K.projectedMetricComplex.Seam)
    (bank : K.projectedMetricComplex.BoundaryBank retain)
    (x : (K.projectedMetricComplex.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ K.projectedMetricComplex.IsVertex (K.projectedMetricComplex.edgePoint bank.val x))
    (fine : E.originalProjectedComplex.Vertex (E.originalRetain retain))
    (at_point : (E.originalProjectedSubdivision_conforming retain).metricEquiv
      (E.originalProjectedComplex.vertexPoint (E.originalRetain retain) fine) =
        K.projectedMetricComplex.bankMap retain bank x) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain) fine = Real.pi := by
  obtain ⟨w, apex, angle⟩ := E.original_projected_totalAngle_of_single_representative retain
    bank.val.face
    ((K.projectedMetricComplex.triangle bank.val.face).edgeMap bank.val.edge x) fine at_point
      (fun b equal =>
      ((K.projectedMetricComplex.point_eq_iff_of_boundary bank.property regular
        (K.projectedMetricComplex.edgePoint_onEdge bank.val x)).mp
        equal.symm).symm)
  exact angle.trans (E.facePieceProjected_totalAngle_at_noncorner_boundary bank.val.face w
    (apex.symm ▸ (K.projectedMetricComplex.triangle bank.val.face).edge_subset_frontier
      bank.val.edge x.property)
    (apex.symm ▸ regular))

open Classical in
/-- Refinement of an original bank introduces no extra real exterior rolling turn. -/
theorem original_projected_bank_inserted_turn_eq_zero (retain : Set K.projectedMetricComplex.Seam)
    (bank : K.projectedMetricComplex.BoundaryBank retain)
    (x : (K.projectedMetricComplex.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ K.projectedMetricComplex.IsVertex (K.projectedMetricComplex.edgePoint bank.val x))
    (fine : E.originalProjectedComplex.Vertex (E.originalRetain retain))
    (at_point : (E.originalProjectedSubdivision_conforming retain).metricEquiv
      (E.originalProjectedComplex.vertexPoint (E.originalRetain retain) fine) =
        K.projectedMetricComplex.bankMap retain bank x) :
    Real.pi - E.originalProjectedComplex.totalAngle (E.originalRetain retain) fine = 0 := by
  rw [E.original_projected_totalAngle_at_bank_interior retain bank x regular fine at_point,
    sub_self]

end Unfoldings.ConvexRoof.CompletionMesh
