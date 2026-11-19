module

public import Unfoldings.Complex.AngleCutSums
public import Unfoldings.Complex.BoundaryOrdering

/-! Compare fan angles across two nested retained seam sets. -/

@[expose] public section

noncomputable section


namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam}

open scoped Classical in
/-- The loss along a specified fan under further cuts is the sum of the original
small copies discarded from that fan. This applies even when several incident seams change. -/
theorem totalAngle_sub_of_nested_copies {medium : Set C.Seam}
    (small_medium : small ⊆ medium) (medium_large : medium ⊆ large)
    (v : C.Vertex medium) :
    C.totalAngle large (C.vertexForgetCuts medium_large v) - C.totalAngle medium v =
      ∑ w ∈ Finset.univ.filter (fun w : C.Vertex small =>
        C.vertexForgetCuts (small_medium.trans medium_large) w =
          C.vertexForgetCuts medium_large v ∧ C.vertexForgetCuts small_medium w ≠ v),
        C.totalAngle small w := by
  classical
  let previous : Finset (C.Vertex small) := Finset.univ.filter
    (fun w => C.vertexForgetCuts (small_medium.trans medium_large) w =
      C.vertexForgetCuts medium_large v)
  let next : Finset (C.Vertex small) := Finset.univ.filter
    (fun w => C.vertexForgetCuts small_medium w = v)
  have nested : next ⊆ previous := by
    intro w hw
    have same : C.vertexForgetCuts small_medium w = v := (Finset.mem_filter.mp hw).2
    have commute : C.vertexForgetCuts (small_medium.trans medium_large) w =
        C.vertexForgetCuts medium_large (C.vertexForgetCuts small_medium w) := by
      obtain ⟨c, rfl⟩ := Quotient.exists_rep w
      rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, commute.trans (congrArg _ same)⟩
  have discarded : previous \ next = Finset.univ.filter (fun w : C.Vertex small =>
      C.vertexForgetCuts (small_medium.trans medium_large) w =
        C.vertexForgetCuts medium_large v ∧ C.vertexForgetCuts small_medium w ≠ v) := by
    ext w
    simp [previous, next]
  have earlier := C.sum_totalAngle_vertexForgetCuts (small_medium.trans medium_large)
    (C.vertexForgetCuts medium_large v)
  have later := C.sum_totalAngle_vertexForgetCuts small_medium v
  rw [← Finset.sum_filter] at earlier later
  rw [← earlier, ← later, ← discarded]
  exact (eq_sub_iff_add_eq.mpr (Finset.sum_sdiff nested)).symm

open scoped Classical in
/-- If two saved fans use the same directed original bank, the angle difference
is carried exactly by the final roof copies that have left that fan. -/
theorem boundaryFanAngle_sub_of_nested_copies {medium : Set C.Seam}
    (small_medium : small ⊆ medium) (medium_large : medium ⊆ large)
    (before : C.BoundaryEnd large) (after : C.BoundaryEnd medium)
    (same_bank : before.val = after.val) :
    let v := C.boundaryEndVertex medium after
    let w := C.boundaryEndVertex large before
    C.totalAngle large w - C.totalAngle medium v =
      ∑ u ∈ Finset.univ.filter (fun u : C.Vertex small =>
        C.vertexForgetCuts (small_medium.trans medium_large) u = w ∧
          C.vertexForgetCuts small_medium u ≠ v), C.totalAngle small u := by
  have aligns : C.vertexForgetCuts medium_large (C.boundaryEndVertex medium after) =
      C.boundaryEndVertex large before :=
    congrArg (fun g : C.Germ => C.vertexOfCorner large g.1) same_bank.symm
  have angle := C.totalAngle_sub_of_nested_copies small_medium medium_large
    (C.boundaryEndVertex medium after)
  rw [aligns] at angle
  exact angle

end Unfoldings.TriangleComplex
