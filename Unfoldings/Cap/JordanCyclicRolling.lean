module

public import Unfoldings.Cap.JordanRolling
public import Unfoldings.Cap.JordanContourBankInterval
public import Unfoldings.Geometry.FiniteHeadingWindow

/-! Actual intrinsic rolling identifies geometric arc error with unreduced heading change. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- Real intrinsic minus projected heading, rolling from this actual starting bank. -/
def jordanCyclicRollHeadingError
    (first i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : ℝ :=
  (C.restrictFaces (K.jordanFaces J)).boundaryRollHeading
    ((K.jordanContour jordan contains avoids).rotate (C.restrictFaces (K.jordanFaces J)) first) i -
      (K.jordanProjectedComplex J).boundaryRollHeading
        ((K.jordanProjectedContour jordan contains avoids).rotate
          (K.jordanProjectedComplex J) first) i

include jordan contains avoids in
open Classical in
/-- The actual rotated rolling uses precisely the original physical corner fans. -/
theorem jordanCyclicRollHeadingError_eq_partialSum
    (first i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanCyclicRollHeadingError jordan contains avoids first i =
      Fin.partialSum (fun k => K.jordanContourTurnError jordan contains avoids
        (finCycle first k.succ)) i := by
  let R := C.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  let P := K.jordanProjectedComplex J
  let fan (w : R.Vertex Set.univ) := P.totalAngle Set.univ
    (R.affineProjectionVertexEquiv (fun f => K.projectFaceEquiv f.val)
      (fun s x => K.projectedTriangle_joined s.val x) Set.univ w)
  change Fin.partialSum (fun k : Fin Q.length => Real.pi -
      R.totalAngle Set.univ (R.boundaryEndVertex Set.univ
        (Q.cycle.point (finCycle first k.succ)))) i -
    Fin.partialSum (fun k : Fin Q.length => Real.pi -
      fan (R.boundaryEndVertex Set.univ (Q.cycle.point (finCycle first k.succ)))) i = _
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rw [Fin.partialSum_zero, Fin.partialSum_zero, Fin.partialSum_zero, sub_self]
  · rw [Fin.partialSum_succ, Fin.partialSum_succ, Fin.partialSum_succ]
    have angle := K.jordan_projected_fan_angle
      (R.boundaryEndVertex Set.univ (Q.cycle.point (finCycle first k.succ)))
    change fan (R.boundaryEndVertex Set.univ (Q.cycle.point (finCycle first k.succ))) = _ at angle
    rw [angle]
    change _ = Fin.partialSum _ k.castSucc +
      ((Real.pi - R.totalAngle Set.univ
          (R.boundaryEndVertex Set.univ (Q.cycle.point (finCycle first k.succ)))) -
        (Real.pi - R.regionalCornerSum Set.univ
          (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
          (R.boundaryEndVertex Set.univ (Q.cycle.point (finCycle first k.succ)))))
    linarith

include jordan contains avoids in
open Classical in
/-- The geometric bank comparison is exactly the actual rolled first-to-last heading error. -/
theorem jordanCyclicRollHeadingError_eq_bank_sum {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (first last : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (contacts : bank ∩ rest ⊆ {K.jordanBankPosition jordan contains avoids first,
      K.jordanBankPosition jordan contains avoids last})
    (on_first : K.jordanContourBankOn jordan contains avoids bank first)
    (off_last : ¬ K.jordanContourBankOn jordan contains avoids bank last) :
    K.jordanCyclicRollHeadingError jordan contains avoids first
        ⟨((finCycle first).symm last).val - 1, by omega⟩ =
      ∑ j ∈ K.jordanGeometricBankIndices jordan contains avoids bank
          {K.jordanBankPosition jordan contains avoids first,
            K.jordanBankPosition jordan contains avoids last},
        K.jordanContourTurnError jordan contains avoids j := by
  classical
  rw [K.jordanCyclicRollHeadingError_eq_partialSum]
  rw [partialSum_succ_eq_strict_window
    (fun j => K.jordanContourTurnError jordan contains avoids (finCycle first j))
    ((finCycle first).symm last)]
  let selected := K.jordanGeometricBankIndices jordan contains avoids bank
    {K.jordanBankPosition jordan contains avoids first,
      K.jordanBankPosition jordan contains avoids last}
  let weight := K.jordanContourTurnError jordan contains avoids
  have rotate := Equiv.sum_comp (finCycle first) (fun j => if j ∈ selected then weight j else 0)
  have membership (j) : finCycle first j ∈ selected ↔
      0 < j ∧ j < (finCycle first).symm last :=
    K.jordanGeometricBankIndices_cyclic_interval jordan contains avoids
      bank_closed rest_closed cover first last contacts on_first off_last j
  simp_rw [membership] at rotate
  have selected_sum : (∑ j, if j ∈ selected then weight j else 0) =
      ∑ j ∈ selected, weight j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact rotate.trans selected_sum

end Unfoldings.ConvexCap
