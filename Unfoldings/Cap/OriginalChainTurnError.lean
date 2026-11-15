module

public import Unfoldings.Complex.RestrictedChainCornerWeights
public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Cap.RestrictedSectionSum

/-! Actual intrinsic-minus-projected fan turns on arbitrary original cut banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance originalTurnMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

open Classical in
/-- The actual projected corner sum at a named one-sided cut vertex copy. -/
def projectedCutFanAngle (U : Set Face) (retain : Set (C.restrictFaces U).Seam)
    (w : (C.restrictFaces U).Vertex retain) : ℝ :=
  ∑ a : (C.restrictFaces U).Corner,
    if (C.restrictFaces U).vertexOfCorner retain a = w then
      (K.projectedTriangle a.1.val).cornerAngle a.2 else 0

/-- Actual intrinsic exterior fan turn minus the same original projected exterior turn. -/
def cutBoundaryTurnError (U : Set Face) {retain : Set (C.restrictFaces U).Seam}
    (p : (C.restrictFaces U).BoundaryEnd retain) : ℝ :=
  let w := (C.restrictFaces U).boundaryEndVertex retain p
  (Real.pi - (C.restrictFaces U).totalAngle retain w) -
    (Real.pi - K.projectedCutFanAngle U retain w)

/-- On an uncut face restriction this is the existing actual patch boundary error. -/
theorem cutBoundaryTurnError_univ (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) :
    K.cutBoundaryTurnError U p = K.restrictedBoundaryTurnError U p := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  have angle : K.projectedCutFanAngle U Set.univ w = R.regionalCornerSum Set.univ
      (fun a => (K.projectedTriangle a.1.val).cornerAngle a.2) w := by
    unfold projectedCutFanAngle TriangleComplex.regionalCornerSum
    apply Finset.sum_congr rfl
    intro a _
    by_cases same : R.vertexOfCorner Set.univ a = w
    · exact (ite_eq_left same).trans (ite_eq_left ⟨Set.mem_univ _, same⟩).symm
    · exact (ite_eq_right same).trans (ite_eq_right (fun both => same both.2)).symm
  exact congrArg (fun angle : ℝ => Real.pi - R.totalAngle Set.univ w - (Real.pi - angle)) angle

variable (U V : Set Face)
  {leftRetain : Set (C.restrictFaces U).Seam}
  {rightRetain : Set (C.restrictFaces V).Seam} {n : ℕ}
  (c : ((C.restrictFaces U).boundarySystem leftRetain).Chain n)
  (d : ((C.restrictFaces V).boundarySystem rightRetain).Chain n)
  (banks : ∀ i, C.includeRestrictedGerm U (c.point i).val =
    C.includeRestrictedGerm V (d.point i).val)

include banks in
/-- Both actual one-sided fan sums are preserved, so the original turn error agrees. -/
theorem cutBoundaryTurnError_eq_of_original_banks (i : Fin n) :
    K.cutBoundaryTurnError U (c.point i.succ) = K.cutBoundaryTurnError V (d.point i.succ) := by
  have intrinsic := C.restricted_boundary_chain_internal_angle U V c d banks i
  have projected := C.sum_restricted_chain_corner_weights_eq U V c d banks
    (fun a => (K.projectedTriangle a.1).cornerAngle a.2) i
  change K.projectedCutFanAngle U leftRetain
      ((C.restrictFaces U).boundaryEndVertex leftRetain (c.point i.succ)) =
    K.projectedCutFanAngle V rightRetain
      ((C.restrictFaces V).boundaryEndVertex rightRetain (d.point i.succ)) at projected
  dsimp only [cutBoundaryTurnError]
  rw [intrinsic, projected]

include banks in
/-- Matching original labels preserve the whole physical projected bank, including its
true terminal endpoint, not just the normalized intrinsic roll. -/
theorem projectedBoundaryChain_eq_of_original_banks :
    K.projectedBoundaryChain U c = K.projectedBoundaryChain V d := by
  apply congrArg (fun vertices : Fin (n + 2) → Plane =>
    (⟨vertices⟩ : PolygonalChain Plane (n + 1)))
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.lastCases_last, Fin.lastCases_last]
    apply K.restricted_boundaryPosition_eq_of_raw
    rw [C.includeRestrictedGerm_boundaryTurn, C.includeRestrictedGerm_boundaryTurn]
    simpa only using! congrArg
      (fun p : C.Germ => C.germOfEndpoint (C.germEdge p) (!p.2)) (banks (Fin.last n))
  · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    exact K.restricted_boundaryPosition_eq_of_raw U V _ _ (banks k)

end Unfoldings.ConvexCap
