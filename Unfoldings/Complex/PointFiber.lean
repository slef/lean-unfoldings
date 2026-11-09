module

public import Unfoldings.Complex.Folding
public import Unfoldings.Complex.Exact
public import Unfoldings.Topology.FiberGraph

/-!
# Bounded seam paths between face copies of one surface point

A spatial folding prevents different points of the same face from being
identified. Thus a surface point has at most one copy in each original face.
Exactness supplies seam connectivity of those copies, and graph loop erasure
gives a seam path shorter than the original face count, even at vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

abbrev PointFiber (retain : Set C.Seam) (x : C.Realization retain) :=
  {a : C.Total // MetricGluing.point C.Cell (C.glue retain) a = x}

def pointFiberGraph (retain : Set C.Seam) (x : C.Realization retain) :
    SimpleGraph (C.PointFiber retain x) :=
  fiberGraph (MetricGluing.point C.Cell (C.glue retain)) (C.glue retain) x

theorem pointFiberGraph_adj_iff (retain : Set C.Seam) (x : C.Realization retain)
    (a b : C.PointFiber retain x) :
    (C.pointFiberGraph retain x).Adj a b ↔ a ≠ b ∧ C.Crosses retain a.val b.val := by
  exact and_congr_right (fun _ => (C.crosses_iff retain a.val b.val).symm)

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F

theorem pointFiber_face_injective (retain : Set C.Seam) (x : C.Realization retain) :
    Function.Injective (fun a : C.PointFiber retain x => a.val.1) := by
  rintro ⟨⟨f, a⟩, ha⟩ ⟨⟨g, b⟩, hb⟩ equal
  change f = g at equal
  subst g
  have image : C.faceMap retain f a = C.faceMap retain f b := ha.trans hb.symm
  have points : a = b := (F.faceMap_isometry retain f).injective image
  subst b
  rfl

@[instance_reducible] def pointFiberFintype (retain : Set C.Seam) (x : C.Realization retain) :
    Fintype (C.PointFiber retain x) :=
  Fintype.ofInjective (fun a : C.PointFiber retain x => a.val.1)
    (F.pointFiber_face_injective retain x)

theorem exists_short_pointFiber_path (retain : Set C.Seam) (x : C.Realization retain)
    (a b : C.PointFiber retain x) :
    ∃ p : (C.pointFiberGraph retain x).Path a b, p.val.length < Fintype.card Face := by
  let := F.pointFiberFintype retain x
  have related : Relation.EqvGen (C.glue retain) a.val b.val :=
    (C.point_eq_iff retain a.val b.val).mp (a.property.trans b.property.symm)
  obtain ⟨p, short⟩ := fiberGraph_exists_short_path
    (MetricGluing.point C.Cell (C.glue retain)) (C.glue retain)
    (fun _ _ h => MetricGluing.point_eq_of_glue C.Cell h) a b related
  exact ⟨p, short.trans_le (Fintype.card_le_of_injective _ (F.pointFiber_face_injective retain x))⟩

end Unfoldings.SpatialFolding
