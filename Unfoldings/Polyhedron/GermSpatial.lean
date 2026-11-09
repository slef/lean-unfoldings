module

public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Cone.Spatial
public import Unfoldings.Complex.LinkConnectivity

/-!
# Actual spatial far endpoints of link germs

Rigid folding sends the far endpoint of a corner germ to the actual other
spatial endpoint of its local edge. Seam crossings preserve these points,
including endpoint reversals. The same holds for the derived mate pairing.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

def germFarPoint (p : C.Germ) : Space :=
  F.place p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2)

theorem linkGerm_apex (retain : Set C.Seam) (v : C.Vertex retain)
    (p : C.LinkGerm retain v) :
    F.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2) =
      F.toSpace retain (C.vertexPoint retain v) :=
  congrArg (fun w : C.Vertex retain => F.toSpace retain (C.vertexPoint retain w)) p.property

theorem germFarPoint_ne_apex (p : C.Germ) :
    F.germFarPoint p ≠ F.place p.1.1 ((C.triangle p.1.1).vertex p.1.2) := by
  intro equal
  have index := (C.triangle p.1.1).vertex_injective ((F.place p.1.1).injective equal)
  exact C.germFarCorner_ne p (Prod.ext rfl index)

theorem linkGerm_far_ne_apex (retain : Set C.Seam) (v : C.Vertex retain)
    (p : C.LinkGerm retain v) :
    F.germFarPoint p.val ≠ F.toSpace retain (C.vertexPoint retain v) := by
  rw [← F.linkGerm_apex retain v p]
  exact F.germFarPoint_ne_apex p.val

theorem germFarPoint_germOfEndpoint (e : EdgeRef Face) (b : Bool) :
    F.germFarPoint (C.germOfEndpoint e b) =
      F.place e.face ((C.triangle e.face).endpoint e.edge (!b)).val := by
  change F.place e.face ((C.triangle e.face).vertex
    (C.germFarCorner (C.germOfEndpoint e b)).2) = _
  rw [C.germFarCorner_germOfEndpoint]
  cases b <;> rfl

theorem germFarPoint_of_crossing {retain : Set C.Seam} {p q : C.Germ}
    (crossing : C.GermCrosses retain p q) : F.germFarPoint p = F.germFarPoint q := by
  obtain ⟨s, _kept, side, b, rfl, rfl⟩ := crossing
  rw [F.germFarPoint_germOfEndpoint, F.germFarPoint_germOfEndpoint,
    ← C.acrossEndpoint_not, C.endpoint_acrossEndpoint]
  exact F.place_across s side ((C.triangle (C.seamSide s side).face).endpoint
    (C.seamSide s side).edge (!b))

theorem germFarPoint_mate (retain : Set C.Seam) (p : C.Germ) :
    F.germFarPoint (C.mateGerm retain p) = F.germFarPoint p := by
  classical
  by_cases paired : ∃ q, C.GermCrosses retain p q
  · obtain ⟨q, crossing⟩ := paired
    rw [C.mateGerm_of_crossing crossing]
    exact (F.germFarPoint_of_crossing crossing).symm
  · simp only [TriangleComplex.mateGerm, dite_eq_right paired]

end Unfoldings.SpatialFolding
