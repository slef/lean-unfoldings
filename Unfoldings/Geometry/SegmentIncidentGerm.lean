module

public import Unfoldings.Geometry.SegmentEndpointGerm

/-! Vertex cut directions are precisely the actual incident segment rays. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

/-- An actual segment avoiding the chosen point in its relative interior contributes
only its original incident endpoint rays to the local cut germ. -/
theorem segment_cellGerm_of_not_mem_openSegment (a b x : Plane)
    (not_open : x ∉ openSegment ℝ a b) :
    AffineArrangement.cellGerm (segmentInequalities a b) (fun _ => true) x =
      (if x = a then nonnegativeRay (b - x) else ∅) ∪
      (if x = b then nonnegativeRay (a - x) else ∅) := by
  classical
  by_cases first : x = a
  · subst x
    rw [segment_cellGerm_start]
    by_cases last : a = b
    · subst b
      simp only [ite_true, Set.union_self]
    · simp only [ite_true, ite_eq_right last, Set.union_empty]
  · by_cases last : x = b
    · subst x
      rw [segment_cellGerm_finish]
      simp only [ite_eq_right first, ite_true, Set.empty_union]
    · have outside : x ∉ segment ℝ a b := by
        intro member
        rw [segment_eq_image_lineMap] at member
        obtain ⟨t, bounds, equal⟩ := member
        have positive : 0 < t := by
          apply lt_of_le_of_ne bounds.1
          intro zero
          have endpoint : a = x := by simpa only [← zero, AffineMap.lineMap_apply_zero] using equal
          exact first endpoint.symm
        have before : t < 1 := by
          apply lt_of_le_of_ne bounds.2
          intro one
          have endpoint : b = x := by simpa only [one, AffineMap.lineMap_apply_one] using equal
          exact last endpoint.symm
        apply not_open
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨positive, before⟩, equal⟩
      have absent : x ∉ AffineArrangement.closedChamber (segmentInequalities a b)
          (fun _ => true) := by rwa [← segment_eq_closedChamber]
      simp only [AffineArrangement.cellGerm, ite_eq_right absent, ite_eq_right first,
        ite_eq_right last, Set.empty_union]

variable {K : Type*} [Finite K] (first last : K → Plane)

/-- Geometric incident vectors, with the original endpoint incidence kept explicit. -/
def incidentSegmentDirections (x : Plane) : Set Plane :=
  ⋃ k, (if x = first k then nonnegativeRay (last k - x) else ∅) ∪
    (if x = last k then nonnegativeRay (first k - x) else ∅)

/-- The exact local cut germ of any finite embedded segment network at one of its vertices. -/
theorem eventually_mem_segment_union_iff_incident (x : Plane)
    (avoids : ∀ k, x ∉ openSegment ℝ (first k) (last k)) :
    ∀ᶠ z in 𝓝 x, z ∈ (⋃ k, segment ℝ (first k) (last k)) ↔
      z - x ∈ incidentSegmentDirections first last x := by
  have near := Filter.eventually_all.mpr (fun k =>
    AffineArrangement.eventually_mem_closedChamber_iff_cellGerm
      (segmentInequalities (first k) (last k)) (fun _ => true) x)
  filter_upwards [near] with z hz
  simp only [← segment_eq_closedChamber,
    segment_cellGerm_of_not_mem_openSegment _ _ x (avoids _)] at hz
  simp only [Set.mem_iUnion, incidentSegmentDirections, hz]

end Unfoldings
