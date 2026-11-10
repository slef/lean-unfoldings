module

public import Unfoldings.Complex.SubdivisionMetric

/-! Identity and iterated conforming refinements, with compatible intrinsic isometries. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z a b

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {Grandchild : Type a} [Fintype Grandchild]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {E : TriangleComplex.{a, b} Grandchild}

def id (C : TriangleComplex.{u, v} Face) : C.Subdivision C where
  parent := fun f => f
  place := fun _ => AffineIsometryEquiv.refl ℝ Plane
  inside _ _ member := member
  cover f x := ⟨f, x, rfl, rfl⟩

@[simp] theorem id_parentPoint (x : C.Total) : (id C).parentPoint x = x := by
  obtain ⟨f, x⟩ := x
  rfl

theorem id_conforming (retain : Set C.Seam) : (id C).Conforming retain retain where
  respects a b joined := by
    rw [id_parentPoint, id_parentPoint]
    exact Relation.EqvGen.rel _ _ joined
  lifts a b related := by simpa only [id_parentPoint] using related

def comp (S : C.Subdivision D) (T : D.Subdivision E) : C.Subdivision E where
  parent k := S.parent (T.parent k)
  place k := (T.place k).trans (S.place (T.parent k))
  inside k x member := S.inside (T.parent k) _ (T.inside k x member)
  cover f x := by
    obtain ⟨g, y, outer_parent, outer_point⟩ := S.cover f x
    obtain ⟨k, z, inner_parent, inner_point⟩ := T.cover g y
    refine ⟨k, z, (congrArg S.parent inner_parent).trans outer_parent, ?_⟩
    change S.place (T.parent k) (T.place k z.val) = x.val
    rw [inner_parent, inner_point, outer_point]

@[simp] theorem comp_parentPoint (S : C.Subdivision D) (T : D.Subdivision E) (x : E.Total) :
    (S.comp T).parentPoint x = S.parentPoint (T.parentPoint x) := rfl

theorem Conforming.comp {S : C.Subdivision D} {T : D.Subdivision E}
    {retain : Set C.Seam} {fineRetain : Set D.Seam} {lastRetain : Set E.Seam}
    (H : S.Conforming retain fineRetain) (K : T.Conforming fineRetain lastRetain) :
    (S.comp T).Conforming retain lastRetain where
  respects a b joined := by
    rw [comp_parentPoint, comp_parentPoint]
    exact (H.related_iff _ _).mp (K.respects a b joined)
  lifts a b related := by
    rw [comp_parentPoint, comp_parentPoint] at related
    exact K.lifts a b ((H.related_iff _ _).mpr related)

theorem Conforming.comp_metricEquiv {S : C.Subdivision D} {T : D.Subdivision E}
    {retain : Set C.Seam} {fineRetain : Set D.Seam} {lastRetain : Set E.Seam}
    (H : S.Conforming retain fineRetain) (K : T.Conforming fineRetain lastRetain)
    (x : E.Realization lastRetain) :
    (H.comp K).metricEquiv x = H.metricEquiv (K.metricEquiv x) := by
  obtain ⟨⟨k, y⟩, rfl⟩ := MetricGluing.point_surjective E.Cell (E.glue lastRetain) x
  rfl

end Unfoldings.TriangleComplex.Subdivision
