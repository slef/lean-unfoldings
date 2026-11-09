module

public import Unfoldings.Cone.SeamBoundary
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Every nonnegative radius occurs on an actual radial seam

Use the opposite endpoint of the original paired edge and scale by the edge
length. This gives actual tangent-glue witnesses at any prescribed radius,
with exactly matching radii on both incident wedges.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def tangentSeamOtherEndpoint (s : C.TangentSeam retain v) : C.TangentDomain retain v s :=
  (C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint
    (C.seamSide s.val.1 s.val.2.1).edge (!s.val.2.2)

def tangentSeamLength (s : C.TangentSeam retain v) : ℝ :=
  dist ((C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint
    (C.seamSide s.val.1 s.val.2.1).edge s.val.2.2)
    (C.tangentSeamOtherEndpoint retain v s)

theorem tangentSeamLength_pos (s : C.TangentSeam retain v) :
    0 < C.tangentSeamLength retain v s := by
  apply dist_pos.mpr
  intro equal
  have endpoints := (C.triangle (C.seamSide s.val.1 s.val.2.1).face).endpoint_injective
    (C.seamSide s.val.1 s.val.2.1).edge equal
  have different : s.val.2.2 ≠ !s.val.2.2 := by cases s.val.2.2 <;> decide
  exact different endpoints

def tangentSeamPointLeft (s : C.TangentSeam retain v) (r : ℝ≥0) :
    C.TangentCell retain v (C.tangentLeft retain v s) :=
  C.tangentLeftPoint retain v s (C.tangentSeamOtherEndpoint retain v s)
    ((r : ℝ) / C.tangentSeamLength retain v s)
    (div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le)

def tangentSeamPointRight (s : C.TangentSeam retain v) (r : ℝ≥0) :
    C.TangentCell retain v (C.tangentRight retain v s) :=
  C.tangentRightPoint retain v s (C.tangentSeamOtherEndpoint retain v s)
    ((r : ℝ) / C.tangentSeamLength retain v s)
    (div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le)

theorem tangentSeamPoints_glue (s : C.TangentSeam retain v) (r : ℝ≥0) :
    C.tangentGlue retain v
      ⟨C.tangentLeft retain v s, C.tangentSeamPointLeft retain v s r⟩
      ⟨C.tangentRight retain v s, C.tangentSeamPointRight retain v s r⟩ :=
  ⟨s, C.tangentSeamOtherEndpoint retain v s, (r : ℝ) / C.tangentSeamLength retain v s,
    div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le, rfl, rfl⟩

theorem tangentSeamPointLeft_radius (s : C.TangentSeam retain v) (r : ℝ≥0) :
    dist (C.tangentApex retain v (C.tangentLeft retain v s))
      (C.tangentSeamPointLeft retain v s r) = (r : ℝ) := by
  change dist (C.tangentApex retain v (C.tangentLeft retain v s)).val
    (AffineMap.lineMap (C.tangentApex retain v (C.tangentLeft retain v s)).val
      (C.tangentSeamOtherEndpoint retain v s).val
      ((r : ℝ) / C.tangentSeamLength retain v s)) = _
  rw [C.tangentLeft_apex_endpoint, dist_left_lineMap,
    Real.norm_of_nonneg (div_nonneg r.coe_nonneg (C.tangentSeamLength_pos retain v s).le)]
  change ((r : ℝ) / C.tangentSeamLength retain v s) * C.tangentSeamLength retain v s = _
  exact div_mul_cancel₀ _ (C.tangentSeamLength_pos retain v s).ne'

theorem tangentSeamPointRight_radius (s : C.TangentSeam retain v) (r : ℝ≥0) :
    dist (C.tangentApex retain v (C.tangentRight retain v s))
      (C.tangentSeamPointRight retain v s r) = (r : ℝ) := by
  have compatible := C.tangentCellRadius_compatible retain v _ _
    (C.tangentSeamPoints_glue retain v s r)
  change dist (C.tangentSeamPointLeft retain v s r)
      (C.tangentApex retain v (C.tangentLeft retain v s)) =
    dist (C.tangentSeamPointRight retain v s r)
      (C.tangentApex retain v (C.tangentRight retain v s)) at compatible
  rw [dist_comm (C.tangentSeamPointLeft retain v s r),
    dist_comm (C.tangentSeamPointRight retain v s r)] at compatible
  exact compatible.symm.trans (C.tangentSeamPointLeft_radius retain v s r)

end Unfoldings.TriangleComplex
