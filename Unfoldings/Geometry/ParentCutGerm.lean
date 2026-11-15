module

public import Unfoldings.Geometry.SegmentIncidentGerm
public import Unfoldings.Geometry.ParentSegments
public import Unfoldings.Geometry.IncidentDirectionCircle

/-! Exact original parent and child cut rays at every vertex of an embedded parent forest. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V) (point : V → Plane)
  (injective : Function.Injective point)

open Classical in
/-- The actual outgoing parent ray and all incoming child rays, with original labels. -/
def vertexCutDirections (w : V) : Set Plane :=
  (if w ∉ P.roots then nonnegativeRay (point (P.parent w) - point w) else ∅) ∪
    ⋃ c : {v : V // v ∉ P.roots},
      if P.parent c.val = w then nonnegativeRay (point c.val - point w) else ∅

include injective in
omit [Finite V] in
theorem incidentSegmentDirections_eq_vertexCutDirections (w : V) :
    incidentSegmentDirections
      (fun c : {v : V // v ∉ P.roots} => point c.val)
      (fun c => point (P.parent c.val)) (point w) = P.vertexCutDirections point w := by
  classical
  ext v
  constructor
  · intro member
    obtain ⟨c, member⟩ := Set.mem_iUnion.mp member
    rcases member with outgoing | incoming
    · by_cases same : point w = point c.val
      · have same_vertex := injective same
        subst w
        apply Or.inl
        simpa only [ite_eq_left c.property, ite_true] using outgoing
      · simp only [ite_eq_right same, Set.mem_empty_iff_false] at outgoing
    · by_cases same : point w = point (P.parent c.val)
      · have parent : P.parent c.val = w := (injective same).symm
        apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨c, ?_⟩
        simpa only [ite_eq_left parent] using
          (show v ∈ nonnegativeRay (point c.val - point w) from
            by simpa only [ite_eq_left same] using incoming)
      · simp only [ite_eq_right same, Set.mem_empty_iff_false] at incoming
  · intro member
    rcases member with outgoing | incoming
    · by_cases nonroot : w ∉ P.roots
      · refine Set.mem_iUnion.mpr ⟨⟨w, nonroot⟩, Or.inl ?_⟩
        simpa only [ite_true] using
          (show v ∈ nonnegativeRay (point (P.parent w) - point w) from
            by simpa only [ite_eq_left nonroot] using outgoing)
      · simp only [ite_eq_right nonroot, Set.mem_empty_iff_false] at outgoing
    · obtain ⟨c, incoming⟩ := Set.mem_iUnion.mp incoming
      by_cases parent : P.parent c.val = w
      · refine Set.mem_iUnion.mpr ⟨c, Or.inr ?_⟩
        have same : point w = point (P.parent c.val) := congrArg point parent.symm
        simpa only [ite_eq_left same] using
          (show v ∈ nonnegativeRay (point c.val - point w) from
            by simpa only [ite_eq_left parent] using incoming)
      · simp only [ite_eq_right parent, Set.mem_empty_iff_false] at incoming

include injective in
/-- The geometric local cut model keeps the exact original parent/child labels at branching. -/
theorem eventually_mem_parent_cuts_iff_directions
    (avoids : ∀ v ∉ P.roots, ∀ w, point w ∉ openSegment ℝ (point v) (point (P.parent v)))
    (w : V) :
    ∀ᶠ z in 𝓝 (point w),
      z ∈ (⋃ c : {v : V // v ∉ P.roots}, segment ℝ (point c.val) (point (P.parent c.val))) ↔
        z - point w ∈ P.vertexCutDirections point w := by
  rw [← P.incidentSegmentDirections_eq_vertexCutDirections point injective w]
  exact eventually_mem_segment_union_iff_incident _ _ (point w)
    (fun c => avoids c.val c.property w)

include injective in
theorem finite_vertexCut_unit_directions (w : V) :
    {v : Plane | v ∈ P.vertexCutDirections point w ∧ ‖v‖ = 1}.Finite := by
  rw [← P.incidentSegmentDirections_eq_vertexCutDirections point injective w]
  exact finite_incident_unit_directions _ _ (point w)

end Unfoldings.AscendingParents
