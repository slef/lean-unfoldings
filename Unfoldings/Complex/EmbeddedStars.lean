module

public import Unfoldings.Complex.Folding
public import Unfoldings.Complex.Star
public import Unfoldings.Complex.LinkOrdering

/-! Spatial foldings give at most one central vertex copy in each original triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

include F

/-- A point class has at most one representative inside any original cell. -/
theorem classIn_subsingleton (retain : Set C.Seam) (a : C.Total) (f : Face) :
    (MetricGluing.classIn C.Cell (C.glue retain) a f).Subsingleton := by
  intro x hx y hy
  apply (F.faceMap_isometry retain f).injective
  exact (C.point_eq_iff retain _ _).mpr
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx) hy)

/-- Thus a corner class represented in a cell consists of exactly that one coordinate. -/
theorem classIn_eq_singleton (retain : Set C.Seam) (a : C.Total) (f : Face) (x : C.Cell f)
    (member : x ∈ MetricGluing.classIn C.Cell (C.glue retain) a f) :
    MetricGluing.classIn C.Cell (C.glue retain) a f = {x} := by
  ext y
  constructor
  · intro hy
    exact F.classIn_subsingleton retain a f hy member
  · rintro rfl
    exact member

/-- Distinct corners at a spatially foldable vertex belong to distinct original faces. -/
theorem cornerAt_faces_injective (retain : Set C.Seam) (v : C.Vertex retain) :
    Function.Injective (fun c : C.CornerAt retain v => c.val.1) := by
  rintro ⟨⟨f, i⟩, hi⟩ ⟨⟨g, j⟩, hj⟩ faces
  change f = g at faces
  subst g
  apply Subtype.ext
  change (f, i) = (f, j)
  apply congrArg (Prod.mk f)
  apply (C.triangle f).vertex_injective
  have equal := congrArg (C.vertexPoint retain) (hi.trans hj.symm)
  have cells := (F.faceMap_isometry retain f).injective equal
  exact congrArg Subtype.val cells

end Unfoldings.SpatialFolding
