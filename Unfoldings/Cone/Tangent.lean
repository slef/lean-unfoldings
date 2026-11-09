module

public import Unfoldings.Complex.LinkOrdering
public import Unfoldings.Geometry.Corner

/-!
# The metric tangent fan of an actual retained vertex

Each incident tagged corner supplies its entire supporting wedge. Retained
edge pairings are extended radially for every nonnegative scale, with their
actual endpoint permutation. Distance is constructed by the existing route
metric and separation quotient, without assuming a cone distance formula.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- A tangent cell is the actual supporting wedge of an incident original corner. -/
def TangentCell (c : C.CornerAt retain v) : Type :=
  (C.triangle c.val.1).cornerWedge c.val.2

instance (c : C.CornerAt retain v) : MetricSpace (C.TangentCell retain v c) :=
  inferInstanceAs (MetricSpace ((C.triangle c.val.1).cornerWedge c.val.2))

/-- The apex in each individual tangent cell. -/
def tangentApex (c : C.CornerAt retain v) : C.TangentCell retain v c :=
  ⟨(C.triangle c.val.1).vertex c.val.2, (C.triangle c.val.1).vertex_mem_cornerWedge c.val.2⟩

/-- Radially extend any point of the bounded original triangle into its supporting wedge. -/
def tangentRadialPoint (c : C.CornerAt retain v) (x : C.Cell c.val.1)
    (t : ℝ) (nonnegative : 0 ≤ t) : C.TangentCell retain v c :=
  ⟨AffineMap.lineMap ((C.triangle c.val.1).vertex c.val.2) x.val t, by
    exact (C.triangle c.val.1).lineMap_mem_cornerWedge c.val.2
      ((C.triangle c.val.1).carrier_subset_cornerWedge c.val.2 x.property) nonnegative⟩

@[simp] theorem tangentRadialPoint_zero (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    C.tangentRadialPoint retain v c x 0 (by rfl) = C.tangentApex retain v c := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero _ _

/-- A directed seam together with the endpoint at this vertex. -/
def TangentSeam := {p : C.Seam × Bool × Bool |
  p.1 ∈ retain ∧ C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide p.1 p.2.1) p.2.2).1 = v}

instance : Finite (C.TangentSeam retain v) := inferInstanceAs
  (Finite {p : C.Seam × Bool × Bool |
    p.1 ∈ retain ∧ C.vertexOfCorner retain (C.germOfEndpoint (C.seamSide p.1 p.2.1) p.2.2).1 = v})

instance : Fintype (C.TangentSeam retain v) := Fintype.ofFinite _

/-- Source corner of a radial seam. -/
def tangentLeft (s : C.TangentSeam retain v) : C.CornerAt retain v :=
  ⟨(C.germOfEndpoint (C.seamSide s.val.1 s.val.2.1) s.val.2.2).1, s.property.2⟩

theorem tangentSeam_crosses (s : C.TangentSeam retain v) : C.GermCrosses retain
    (C.germOfEndpoint (C.seamSide s.val.1 s.val.2.1) s.val.2.2)
    (C.germOfEndpoint (C.seamSide s.val.1 (!s.val.2.1))
      (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)) :=
  ⟨s.val.1, s.property.1, s.val.2.1, s.val.2.2, rfl, rfl⟩

/-- Target corner, with endpoint transport proving membership in the same actual vertex class. -/
def tangentRight (s : C.TangentSeam retain v) : C.CornerAt retain v :=
  ⟨(C.germOfEndpoint (C.seamSide s.val.1 (!s.val.2.1))
    (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)).1,
    (GermCrosses.vertex_eq C (C.tangentSeam_crosses retain v s)).symm.trans s.property.2⟩

/-- The original source edge, whose radial extensions fill a tangent seam. -/
abbrev TangentDomain (s : C.TangentSeam retain v) :=
  (C.triangle (C.seamSide s.val.1 s.val.2.1).face).Edge (C.seamSide s.val.1 s.val.2.1).edge

def tangentLeftPoint (s : C.TangentSeam retain v) (x : C.TangentDomain retain v s)
    (t : ℝ) (nonnegative : 0 ≤ t) : C.TangentCell retain v (C.tangentLeft retain v s) :=
  C.tangentRadialPoint retain v (C.tangentLeft retain v s)
    ((C.triangle (C.seamSide s.val.1 s.val.2.1).face).edgeMap
      (C.seamSide s.val.1 s.val.2.1).edge x) t nonnegative

def tangentRightPoint (s : C.TangentSeam retain v) (x : C.TangentDomain retain v s)
    (t : ℝ) (nonnegative : 0 ≤ t) : C.TangentCell retain v (C.tangentRight retain v s) :=
  C.tangentRadialPoint retain v (C.tangentRight retain v s)
    ((C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).edgeMap
      (C.seamSide s.val.1 (!s.val.2.1)).edge (C.across s.val.1 s.val.2.1 x)) t nonnegative

/-- Actual radial extensions of the retained edge isometries, including all scales. -/
def tangentGlue (a b : MetricGluing.Total (C.TangentCell retain v)) : Prop :=
  ∃ s : C.TangentSeam retain v, ∃ x : C.TangentDomain retain v s, ∃ t : ℝ, ∃ h : 0 ≤ t,
    a = ⟨C.tangentLeft retain v s, C.tangentLeftPoint retain v s x t h⟩ ∧
      b = ⟨C.tangentRight retain v s, C.tangentRightPoint retain v s x t h⟩

/-- The tangent fan's constructed extended metric; radial exactness is a later theorem. -/
abbrev TangentFan := MetricGluing.Realization (C.TangentCell retain v) (C.tangentGlue retain v)

def tangentFaceMap (c : C.CornerAt retain v) : C.TangentCell retain v c → C.TangentFan retain v :=
  MetricGluing.of (C.TangentCell retain v) (C.tangentGlue retain v) c

theorem tangentFaceMap_lipschitz (c : C.CornerAt retain v) :
    LipschitzWith 1 (C.tangentFaceMap retain v c) :=
  MetricGluing.of_lipschitz (C.TangentCell retain v) (C.tangentGlue retain v) c

theorem tangentSeam_apex_eq (s : C.TangentSeam retain v) :
    C.tangentFaceMap retain v (C.tangentLeft retain v s)
      (C.tangentApex retain v (C.tangentLeft retain v s)) =
    C.tangentFaceMap retain v (C.tangentRight retain v s)
      (C.tangentApex retain v (C.tangentRight retain v s)) := by
  apply MetricGluing.point_eq_of_glue
  let x : C.TangentDomain retain v s :=
    (C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint
      (C.seamSide s.val.1 s.val.2.1).edge s.val.2.2
  refine ⟨s, x, 0, le_rfl, ?_, ?_⟩
  · apply congrArg (Sigma.mk (C.tangentLeft retain v s))
    apply Subtype.ext
    exact (AffineMap.lineMap_apply_zero _ _).symm
  · apply congrArg (Sigma.mk (C.tangentRight retain v s))
    apply Subtype.ext
    exact (AffineMap.lineMap_apply_zero _ _).symm

end Unfoldings.TriangleComplex
