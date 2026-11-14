module

public import Unfoldings.Cap.JordanRolling
public import Unfoldings.Cap.BankLengthProjection

/-! Exact edgewise heading and speed factors for the actual intrinsically rolled Jordan bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- Actual intrinsic edge length divided by the length of the identical projected bank. -/
def jordanRollStretch (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : ℝ :=
  (C.restrictFaces (K.jordanFaces J)).boundaryBankLength
    ((K.jordanContour jordan contains avoids).cycle.point i) /
      (K.jordanProjectedComplex J).boundaryBankLength
        ((K.jordanProjectedContour jordan contains avoids).cycle.point i)

include jordan contains avoids in
open Classical in
theorem jordan_bank_length_projection
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    let R := C.restrictFaces (K.jordanFaces J)
    let p := (K.jordanContour jordan contains avoids).cycle.point i
    let projected := (K.jordanProjectedComplex J).boundaryBankLength
      ((K.jordanProjectedContour jordan contains avoids).cycle.point i)
    projected ≤ R.boundaryBankLength p ∧
      K.normal p.val.1.1.val 2 * R.boundaryBankLength p ≤ projected := by
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  exact K.germ_length_projection ((p.val.1.1.val, p.val.1.2), p.val.2)

include jordan contains avoids in
open Classical in
/-- Every actual bank speed lies between one and the reciprocal normal-height bound. -/
theorem jordanRollStretch_bounds {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    1 ≤ K.jordanRollStretch jordan contains avoids i ∧
      K.jordanRollStretch jordan contains avoids i ≤ c⁻¹ := by
  let Q := K.jordanContour jordan contains avoids
  let V := K.jordanProjectedContour jordan contains avoids
  let R := C.restrictFaces (K.jordanFaces J)
  let P := K.jordanProjectedComplex J
  have bounds := K.jordan_bank_length_projection jordan contains avoids i
  change P.boundaryBankLength (V.cycle.point i) ≤ R.boundaryBankLength (Q.cycle.point i) ∧
    K.normal (Q.cycle.point i).val.1.1.val 2 * R.boundaryBankLength (Q.cycle.point i) ≤
      P.boundaryBankLength (V.cycle.point i) at bounds
  have length_positive := P.boundaryBankLength_pos (V.cycle.point i)
  change 1 ≤ R.boundaryBankLength (Q.cycle.point i) / P.boundaryBankLength (V.cycle.point i) ∧
    R.boundaryBankLength (Q.cycle.point i) / P.boundaryBankLength (V.cycle.point i) ≤ c⁻¹
  constructor
  · exact (one_le_div₀ length_positive).mpr bounds.1
  · apply (div_le_iff₀ length_positive).mpr
    have lower : c * R.boundaryBankLength (Q.cycle.point i) ≤
        P.boundaryBankLength (V.cycle.point i) :=
      (mul_le_mul_of_nonneg_right (height _) (R.boundaryBankLength_pos _).le).trans bounds.2
    calc
      _ = c⁻¹ * (c * R.boundaryBankLength (Q.cycle.point i)) := by
        rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left lower (inv_nonneg.mpr positive.le)

include jordan contains avoids in
open Classical in
/-- The actual intrinsic and projected bank edges have exactly these speed and real phase errors. -/
theorem jordan_bank_edge_factor
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    ((C.restrictFaces (K.jordanFaces J)).boundaryRoll
      (K.jordanContour jordan contains avoids)).edge i =
      (K.jordanRollStretch jordan contains avoids i : ℂ) *
        polarRay (K.jordanRollHeadingError jordan contains avoids i) *
          ((K.jordanProjectedComplex J).boundaryRoll
            (K.jordanProjectedContour jordan contains avoids)).edge i := by
  let Q := K.jordanContour jordan contains avoids
  let V := K.jordanProjectedContour jordan contains avoids
  let R := C.restrictFaces (K.jordanFaces J)
  let P := K.jordanProjectedComplex J
  let a := R.boundaryBankLength (Q.cycle.point i)
  let b := P.boundaryBankLength (V.cycle.point i)
  let α := R.boundaryRollHeading Q i
  let β := P.boundaryRollHeading V i
  have intrinsic : (R.boundaryRoll Q).edge i = (a : ℂ) * polarRay α :=
    PolygonalChain.ofHeadings_edge _ _ _ i
  have projected : (P.boundaryRoll V).edge i = (b : ℂ) * polarRay β :=
    PolygonalChain.ofHeadings_edge _ _ _ i
  change (R.boundaryRoll Q).edge i = (((a / b : ℝ) : ℂ) * polarRay (α - β)) *
    (P.boundaryRoll V).edge i
  rw [intrinsic, projected]
  have nonzero : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (P.boundaryBankLength_pos _).ne'
  have phase : polarRay (α - β) * polarRay β = polarRay α := by
    rw [← polarRay_add, sub_add_cancel]
  rw [Complex.ofReal_div]
  calc
    _ = ((a : ℂ) / (b : ℂ)) * (b : ℂ) * polarRay α := by rw [div_mul_cancel₀ _ nonzero]
    _ = _ := by rw [← phase]; ring

end Unfoldings.ConvexCap
