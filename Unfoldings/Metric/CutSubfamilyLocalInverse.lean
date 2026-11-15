module

public import Unfoldings.Metric.ConvexCutSubfamily
public import Unfoldings.Metric.LocalSeams

/-! Canonical inverse cell maps for actual cut subfamilies near a retained metric class. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E) (selected : I → Prop)

/-- The actual metric cut of a specified original physical cell subfamily. -/
abbrev CutSubfamily := PolygonalCut (fun i : {i // selected i} => cells i.val)
  (fun i => closed i.val) cuts

open Classical in
/-- Include selected original cell copies; a fallback is used only on omitted cells. -/
def cutSubfamilyCellMap (source : CutSubfamily cells closed cuts selected) (i : I) :
    cells i → CutSubfamily cells closed cuts selected :=
  if h : selected i then
    of (fun i : {i // selected i} => cells i.val)
      (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation
      ⟨i, h⟩
  else fun _ => source

@[simp] theorem cutSubfamilyCellMap_of_selected (source : CutSubfamily cells closed cuts selected)
    (i : I) (member : selected i) (x : cells i) :
    cutSubfamilyCellMap cells closed cuts selected source i x =
      of (fun i : {i // selected i} => cells i.val)
        (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation
        ⟨i, member⟩ x := by
  simp only [cutSubfamilyCellMap, dite_eq_left member]

theorem cutSubfamilyCellMap_lipschitz (source : CutSubfamily cells closed cuts selected) (i : I) :
    LipschitzWith 1 (cutSubfamilyCellMap cells closed cuts selected source i) := by
  classical
  by_cases member : selected i
  · simpa only [cutSubfamilyCellMap, dite_eq_left member] using
      of_lipschitz (fun i : {i // selected i} => cells i.val)
        (cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts).relation
        ⟨i, member⟩
  · simp only [cutSubfamilyCellMap, dite_eq_right member]
    intro x y
    simp only [edist_self, ENNReal.coe_one, one_mul]
    exact bot_le

/-- Keeping all incident cells supplies compatibility on every actual incident seam. -/
theorem cutSubfamilyCellMap_incident_compatible
    (a : Total (fun i => cells i)) (source : CutSubfamily cells closed cuts selected)
    (incident_selected : ∀ i,
      (classIn (fun i => cells i) (cutSeams cells closed cuts).relation a i).Nonempty →
        selected i) :
    ∀ s, (cutSeams cells closed cuts).closedSeams.Incident a s → ∀ x,
      cutSubfamilyCellMap cells closed cuts selected source
        ((cutSeams cells closed cuts).closedSeams.left s)
        ((cutSeams cells closed cuts).closedSeams.toLeft s x) =
      cutSubfamilyCellMap cells closed cuts selected source
        ((cutSeams cells closed cuts).closedSeams.right s)
        ((cutSeams cells closed cuts).closedSeams.toRight s x) := by
  rintro ⟨i, j⟩ ⟨p, related, u, rfl⟩ x
  have first : selected i := incident_selected i ⟨_, related⟩
  have last : selected j := incident_selected j
    ⟨_, Relation.EqvGen.trans _ _ _ related (Relation.EqvGen.rel _ _ ⟨(i, j), u, rfl, rfl⟩)⟩
  change cutSubfamilyCellMap cells closed cuts selected source i
      ⟨x.val, (cutSeams cells closed cuts).subset_left i j x.property⟩ =
    cutSubfamilyCellMap cells closed cuts selected source j
      ⟨x.val, (cutSeams cells closed cuts).subset_right i j x.property⟩
  rw [cutSubfamilyCellMap_of_selected cells closed cuts selected source i first,
    cutSubfamilyCellMap_of_selected cells closed cuts selected source j last]
  apply point_eq_of_glue
  exact ⟨(⟨i, first⟩, ⟨j, last⟩), x, rfl, rfl⟩

end Unfoldings.MetricGluing
