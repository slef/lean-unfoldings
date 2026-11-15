module

public import Unfoldings.Geometry.SegmentEndpointGerm

/-! Exact incident endpoint-ray germs for finite segment families in arbitrary normed spaces. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- Original endpoint incidences retain their actual directions. -/
def segmentIncidentRays {I : Type*} (first last : I → E) (x : E) : Set E :=
  ⋃ i, (if x = first i then nonnegativeRay (last i - x) else ∅) ∪
    (if x = last i then nonnegativeRay (first i - x) else ∅)

open Classical in
/-- A segment avoiding the point in its open part has only its original endpoint-ray germs. -/
theorem eventually_mem_segment_iff_incident_rays (a b x : E)
    (not_open : x ∉ openSegment ℝ a b) :
    ∀ᶠ z in 𝓝 x, z ∈ segment ℝ a b ↔ z - x ∈
      (if x = a then nonnegativeRay (b - x) else ∅) ∪
      (if x = b then nonnegativeRay (a - x) else ∅) := by
  by_cases first : x = a
  · subst x
    by_cases last : a = b
    · subst b
      simpa only [ite_true, Set.union_self] using eventually_mem_segment_iff_nonnegativeRay a a
    · simpa only [ite_true, ite_eq_right last, Set.union_empty] using
        eventually_mem_segment_iff_nonnegativeRay a b
  · by_cases last : x = b
    · subst x
      simpa only [ite_eq_right first, ite_true, Set.empty_union, segment_symm ℝ a b] using
        eventually_mem_segment_iff_nonnegativeRay b a
    · have outside : x ∉ segment ℝ a b := by
        intro member
        rw [segment_eq_image_lineMap] at member
        obtain ⟨t, bounds, equal⟩ := member
        have positive : 0 < t := by
          apply lt_of_le_of_ne bounds.1
          intro zero
          have endpoint : a = x := by
            simpa only [← zero, AffineMap.lineMap_apply_zero] using equal
          exact first endpoint.symm
        have before : t < 1 := by
          apply lt_of_le_of_ne bounds.2
          intro one
          have endpoint : b = x := by
            simpa only [one, AffineMap.lineMap_apply_one] using equal
          exact last endpoint.symm
        exact not_open ((openSegment_eq_image_lineMap ℝ a b).symm ▸ ⟨t, ⟨positive, before⟩, equal⟩)
      have closed : IsClosed (segment ℝ a b) := by
        rw [segment_eq_image_lineMap]
        exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
      filter_upwards [closed.isOpen_compl.mem_nhds outside] with z hz
      simpa only [ite_eq_right first, ite_eq_right last, Set.empty_union,
        Set.mem_empty_iff_false, iff_false, Set.mem_compl_iff] using hz

/-- At a vertex of a finite segment family, the exact local model is its original incident rays. -/
theorem eventually_mem_segment_family_iff_incident_rays {I : Type*} [Finite I]
    (first last : I → E) (x : E) (not_open : ∀ i, x ∉ openSegment ℝ (first i) (last i)) :
    ∀ᶠ z in 𝓝 x, z ∈ (⋃ i, segment ℝ (first i) (last i)) ↔
      z - x ∈ segmentIncidentRays first last x := by
  have near := eventually_all.mpr (fun i =>
    eventually_mem_segment_iff_incident_rays (first i) (last i) x (not_open i))
  filter_upwards [near] with z hz
  simp only [segmentIncidentRays, Set.mem_iUnion, hz]

end Unfoldings
