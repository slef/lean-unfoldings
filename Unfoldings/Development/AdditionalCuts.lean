module

public import Unfoldings.Development

/-! Additional seam cuts preserve all rigid placements and the nonoverlap predicate. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {small large : Set C.Seam} (D : FacewiseDevelopment C large) (inclusion : small ⊆ large)

/-- The same placements give a development after any additional cuts. -/
def cut : FacewiseDevelopment C small where
  place := D.place
  joined s member := D.joined s (inclusion member)
  opposite s member := D.opposite s (inclusion member)

@[simp] theorem cut_place (f : Face) : (D.cut inclusion).place f = D.place f := rfl

@[simp] theorem cut_faceImage (f : Face) : (D.cut inclusion).faceImage f = D.faceImage f := rfl

@[simp] theorem cut_nonoverlapping_iff : (D.cut inclusion).Nonoverlapping ↔ D.Nonoverlapping :=
  Iff.rfl

/-- Forgetting the added cuts commutes with the actual developed metric realization maps. -/
theorem cut_toPlane (x : C.Realization small) :
    (D.cut inclusion).toPlane x = D.toPlane (C.forgetCuts inclusion x) := by
  obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue small) x
  change (D.cut inclusion).toPlane (C.faceMap small f x) =
    D.toPlane (C.forgetCuts inclusion (C.faceMap small f x))
  rw [C.forgetCuts_faceMap, toPlane_faceMap, toPlane_faceMap, cut_place]

end Unfoldings.FacewiseDevelopment
