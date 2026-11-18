module

public import Unfoldings.Complex.RestrictedIncidentCopies
public import Unfoldings.Complex.Angles

/-! Fully retained physical stars preserve every original corner weight under face restriction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

open Classical in
/-- Every corner weight in a complete physical star is unchanged by whole-face restriction. -/
theorem sum_restricted_incident_corner_weights (U : Set Face) (retain : Set C.Seam)
    (position : Space) (incident : ∀ a : C.Total, F.place a.1 a.2.val = position → a.1 ∈ U)
    (w : (C.restrictFaces U).Vertex (C.restrictRetain U retain))
    (at_point : (F.restrictFaces U).toSpace (C.restrictRetain U retain)
      ((C.restrictFaces U).vertexPoint (C.restrictRetain U retain) w) = position)
    (weight : C.Corner → ℝ) :
    (∑ c : C.Corner, if C.vertexOfCorner retain c = C.includeRestrictedVertex U retain w
      then weight c else 0) =
      ∑ d : (C.restrictFaces U).Corner,
        if (C.restrictFaces U).vertexOfCorner (C.restrictRetain U retain) d = w
        then weight (d.1.val, d.2) else 0 := by
  classical
  let R := C.restrictFaces U
  let value (c : C.Corner) : ℝ :=
    if C.vertexOfCorner retain c = C.includeRestrictedVertex U retain w then weight c else 0
  have selected (c : C.Corner)
      (same : C.vertexOfCorner retain c = C.includeRestrictedVertex U retain w) : c.1 ∈ U := by
    apply incident (C.cornerPoint c)
    exact (congrArg (fun v => F.toSpace retain (C.vertexPoint retain v)) same).trans
      ((F.toSpace_includeRestrictedVertex U retain w).trans at_point)
  let e : R.Corner ≃ {c : C.Corner // c.1 ∈ U} := {
    toFun c := ⟨(c.1.val, c.2), c.1.property⟩
    invFun c := (⟨c.val.1, c.property⟩, c.val.2)
    left_inv _ := rfl
    right_inv _ := rfl }
  have same (c : R.Corner) :
      C.vertexOfCorner retain (c.1.val, c.2) = C.includeRestrictedVertex U retain w ↔
        R.vertexOfCorner (C.restrictRetain U retain) c = w := by
    constructor
    · intro equal
      exact (F.includeRestrictedVertex_injective_at U retain position incident w
        (R.vertexOfCorner (C.restrictRetain U retain) c) at_point equal.symm).symm
    · intro equal
      exact congrArg (C.includeRestrictedVertex U retain) equal
  calc
    _ = ∑ c : C.Corner, if c.1 ∈ U then value c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases equal : C.vertexOfCorner retain c = C.includeRestrictedVertex U retain w
      · simp only [equal, selected c equal, ite_true, value]
      · simp only [value, equal, ite_false, ite_self]
    _ = ∑ c : {c : C.Corner // c.1 ∈ U}, value c.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) value
    _ = ∑ c : R.Corner, value (e c).val :=
      (Equiv.sum_comp e (fun c => value c.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      change (if C.vertexOfCorner retain (c.1.val, c.2) =
          C.includeRestrictedVertex U retain w then weight (c.1.val, c.2) else 0) = _
      rw [same c]

open Classical in
/-- A complete incident physical star retains its exact one-sided intrinsic angle. -/
theorem restricted_incident_totalAngle (U : Set Face) (retain : Set C.Seam)
    (position : Space) (incident : ∀ a : C.Total, F.place a.1 a.2.val = position → a.1 ∈ U)
    (w : (C.restrictFaces U).Vertex (C.restrictRetain U retain))
    (at_point : (F.restrictFaces U).toSpace (C.restrictRetain U retain)
      ((C.restrictFaces U).vertexPoint (C.restrictRetain U retain) w) = position) :
    C.totalAngle retain (C.includeRestrictedVertex U retain w) =
      (C.restrictFaces U).totalAngle (C.restrictRetain U retain) w :=
  F.sum_restricted_incident_corner_weights U retain position incident w at_point
    (fun c => (C.triangle c.1).cornerAngle c.2)

end Unfoldings.SpatialFolding
