module

public import Unfoldings.Complex.FaceRestrictionClasses
public import Unfoldings.Complex.RegionalCorners

/-! Include actual restricted vertex copies and recover their original selected corner sums. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
theorem included_glue_of_restricted (U : Set Face) (retain : Set C.Seam)
    {a b : (C.restrictFaces U).Total}
    (joined : (C.restrictFaces U).glue (C.restrictRetain U retain) a b) :
    C.glue retain (C.includedTotal U a) (C.includedTotal U b) := by
  obtain ⟨s, kept, x, first, last⟩ := joined
  exact ⟨s.val, kept, x, congrArg (C.includedTotal U) first, congrArg (C.includedTotal U) last⟩

open Classical in
theorem included_eqvGen_of_restricted (U : Set Face) (retain : Set C.Seam)
    {a b : (C.restrictFaces U).Total}
    (related : Relation.EqvGen ((C.restrictFaces U).glue (C.restrictRetain U retain)) a b) :
    Relation.EqvGen (C.glue retain) (C.includedTotal U a) (C.includedTotal U b) := by
  induction related with
  | rel a b h => exact Relation.EqvGen.rel _ _ (C.included_glue_of_restricted U retain h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ first last => exact Relation.EqvGen.trans _ _ _ first last

open Classical in
/-- Face restriction can split old vertices; every resulting copy retains its original class. -/
def includeRestrictedVertex (U : Set Face) (retain : Set C.Seam) :
    (C.restrictFaces U).Vertex (C.restrictRetain U retain) → C.Vertex retain :=
  Quotient.map (fun c => (c.1.val, c.2))
    (fun _ _ related => C.included_eqvGen_of_restricted U retain related)

open Classical in
@[simp] theorem includeRestrictedVertex_ofCorner (U : Set Face) (retain : Set C.Seam)
    (c : (C.restrictFaces U).Corner) :
    C.includeRestrictedVertex U retain
      ((C.restrictFaces U).vertexOfCorner (C.restrictRetain U retain) c) =
        C.vertexOfCorner retain (c.1.val, c.2) := rfl

open Classical in
/-- The all-seams inclusion has an explicit uncut domain, avoiding dependent retain-set casts. -/
def includeRestrictedVertexUniv (U : Set Face) :
    (C.restrictFaces U).Vertex Set.univ → C.Vertex Set.univ :=
  Quotient.map (fun c => (c.1.val, c.2)) (by
    intro a b related
    have kept : C.restrictRetain U Set.univ = Set.univ := by ext s; rfl
    change Relation.EqvGen (C.glue Set.univ)
      (C.cornerPoint (a.1.val, a.2)) (C.cornerPoint (b.1.val, b.2))
    have related' : Relation.EqvGen ((C.restrictFaces U).glue (C.restrictRetain U Set.univ))
        ((C.restrictFaces U).cornerPoint a) ((C.restrictFaces U).cornerPoint b) := by
      rw [kept]
      exact related
    exact C.included_eqvGen_of_restricted U Set.univ related')

open Classical in
@[simp] theorem includeRestrictedVertex_ofCorner_univ (U : Set Face)
    (c : (C.restrictFaces U).Corner) :
    C.includeRestrictedVertexUniv U ((C.restrictFaces U).vertexOfCorner Set.univ c) =
      C.vertexOfCorner Set.univ (c.1.val, c.2) := rfl

open Classical in
/-- The actual restricted copy angles sum exactly to the selected original corner contributions. -/
theorem totalAngle_restricted_vertex_fiber (U : Set Face) (w : C.Vertex Set.univ) :
    (∑ z : (C.restrictFaces U).Vertex Set.univ,
      if C.includeRestrictedVertexUniv U z = w then
        (C.restrictFaces U).totalAngle Set.univ z else 0) =
          C.regionalCornerSum U (fun c => (C.triangle c.1).cornerAngle c.2) w := by
  classical
  let R := C.restrictFaces U
  calc
    _ = ∑ z : R.Vertex Set.univ, ∑ c : R.Corner,
        if R.vertexOfCorner Set.univ c = z ∧ C.includeRestrictedVertexUniv U z = w then
          (R.triangle c.1).cornerAngle c.2 else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases same : C.includeRestrictedVertexUniv U z = w
      · simp only [R, same, and_true, ite_true, totalAngle]
      · simp only [R, same, and_false, ite_false, Finset.sum_const_zero]
    _ = ∑ c : R.Corner, ∑ z : R.Vertex Set.univ,
        if R.vertexOfCorner Set.univ c = z ∧ C.includeRestrictedVertexUniv U z = w then
          (R.triangle c.1).cornerAngle c.2 else 0 := Finset.sum_comm
    _ = ∑ c : R.Corner,
        if C.vertexOfCorner Set.univ (c.1.val, c.2) = w then
          (C.triangle c.1.val).cornerAngle c.2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      change (∑ z : R.Vertex Set.univ,
        if R.vertexOfCorner Set.univ c = z ∧ C.includeRestrictedVertexUniv U z = w then
          (C.triangle c.1.val).cornerAngle c.2 else 0) = _
      simp [R, ite_and]
      rfl
    _ = _ := by
      rw [regionalCornerSum, Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [← Finset.sum_subtype (p := fun f => f ∈ U)
        (Finset.univ.filter (· ∈ U)) (by simp)
        (fun f => ∑ k : Fin 3, if C.vertexOfCorner Set.univ (f, k) = w then
          (C.triangle f).cornerAngle k else 0), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      by_cases present : f ∈ U <;> simp [present]

end Unfoldings.TriangleComplex
