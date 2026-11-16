module

public import Unfoldings.Metric.CutSubfamilyLocalInverse

/-! Keeping every original incident cell preserves the entire original metric fiber. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E) (selected : I → Prop)

/-- The subfamily inclusion cannot merge any copies in a fully retained incident class,
even copies arbitrarily far apart in the subfamily's intrinsic metric. -/
theorem cutSubfamilyMap_injective_at
    (a : Total (fun i : {i // selected i} => cells i.val))
    (incident_selected : ∀ i,
      (classIn (fun i => cells i) (cutSeams cells closed cuts).relation ⟨a.1.val, a.2⟩ i).Nonempty →
        selected i)
    (y : CutSubfamily cells closed cuts selected)
    (equal : cutSubfamilyMap cells closed cuts selected
      (point (fun i : {i // selected i} => cells i.val)
        (cutSeams (fun i : {i // selected i} => cells i.val)
          (fun i => closed i.val) cuts).relation a) =
      cutSubfamilyMap cells closed cuts selected y) :
    point (fun i : {i // selected i} => cells i.val)
      (cutSeams (fun i : {i // selected i} => cells i.val)
        (fun i => closed i.val) cuts).relation a =
        y := by
  obtain ⟨b, rfl⟩ := point_surjective
    (fun i : {i // selected i} => cells i.val)
    (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation y
  let S := cutSeams cells closed cuts
  let source := point (fun i : {i // selected i} => cells i.val)
    (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation a
  let f := cutSubfamilyCellMap cells closed cuts selected source
  have related := S.exact ⟨a.1.val, a.2⟩ ⟨b.1.val, b.2⟩ equal
  have same := S.closedSeams.class_eq_of_incident_compatible ⟨a.1.val, a.2⟩ f
    (cutSubfamilyCellMap_incident_compatible cells closed cuts selected
      ⟨a.1.val, a.2⟩ source incident_selected) related
  exact (cutSubfamilyCellMap_of_selected cells closed cuts selected source a.1.val
    a.1.property a.2).symm.trans (same.trans
      (cutSubfamilyCellMap_of_selected cells closed cuts selected source b.1.val b.1.property b.2))

/-- Retaining every physical cell at the center already preserves its entire metric fiber. -/
theorem cutSubfamilyMap_injective_at_of_cells_at_point
    (x : CutSubfamily cells closed cuts selected)
    (selected_at_point : ∀ i,
      (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).fold x ∈
        cells i → selected i)
    (y : CutSubfamily cells closed cuts selected)
    (equal : cutSubfamilyMap cells closed cuts selected x =
      cutSubfamilyMap cells closed cuts selected y) : x = y := by
  obtain ⟨a, rfl⟩ := point_surjective
    (fun i : {i // selected i} => cells i.val)
    (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation x
  apply cutSubfamilyMap_injective_at cells closed cuts selected a _ y equal
  rintro i ⟨p, related⟩
  apply selected_at_point i
  have physical := (cutSeams cells closed cuts).physical_eq_of_eqvGen related
  exact Eq.mpr (congrArg (fun z : E => z ∈ cells i) physical) p.property

end Unfoldings.MetricGluing
