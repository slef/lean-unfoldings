module

public import Unfoldings.Cap.RestrictedSectionDirections
public import Unfoldings.Cap.ProjectedInterval

/-! Supporting planes constrain the rays at every genuine crease crossing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ}

/-- The projected ray on one face stays on its side of every other incident
support plane. -/
theorem projectedGermRay_normalSlope_side (p q : C.LinkGerm Set.univ w) :
    0 ≤ inner ℝ (K.normalSlope p.val.1.1 - K.normalSlope q.val.1.1) (K.projectedGermRay p) := by
  have h := K.incident_normal_germ_nonpos (a := ⟨q.val.1, q.property⟩) p
  have pl := mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (K.normal_upward q.val.1.1).le) h
  change (K.normal q.val.1.1 2)⁻¹ *
    inner ℝ (K.normal q.val.1.1) (K.folding.germDirection p.val) ≤ 0 at pl
  rw [← K.normalSlope_inner_add_height, K.horizontal_germDirection] at pl
  have lift := congrArg (fun z : Space => z 2) (K.spatialDirection_horizontal_germ p.val)
  rw [K.spatialDirection_height, K.horizontal_germDirection] at lift
  rw [inner_sub_left]
  linarith only [pl, lift]

/-- At an actual step of a refined fan, the shared ray is tangent to the
difference of the two supporting planes. -/
theorem projectedIntervalRay_normalSlope_tie {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n) (i : Fin n) :
    inner ℝ (K.normalSlope (c.point i.castSucc).val.1.1 -
      K.normalSlope (c.point i.succ).val.1.1) (K.projectedIntervalRay c i.castSucc.succ) = 0 := by
  let p := C.linkTurn Set.univ w (c.point i.castSucc)
  let q := c.point i.succ
  have same : K.projectedGermRay p = K.projectedGermRay q := by
    have h := congrArg K.projectedGermRay (c.next i)
    change K.projectedGermRay (C.linkMate Set.univ w p) = K.projectedGermRay q at h
    simpa only [K.projectedGermRay_mate] using h
  have on_first := K.projectedGermRay_normalSlope_side p q
  have on_second := K.projectedGermRay_normalSlope_side q p
  rw [← same, inner_sub_left] at on_second
  rw [K.projectedIntervalRay_succ]
  change inner ℝ (K.normalSlope p.val.1.1 - K.normalSlope q.val.1.1)
    (K.projectedGermRay p) = 0
  rw [inner_sub_left] at on_first ⊢
  linarith only [on_first, on_second]

end Unfoldings.ConvexCap
