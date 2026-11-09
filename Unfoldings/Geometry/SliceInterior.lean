module

public import Unfoldings.Geometry.RadialSlice

/-!
# Transverse slices through the ambient interior

For a convex body with spatial interior, every positive functional level
below some body point meets the ambient interior, provided the vertex is
in the body. Density of the interior supplies a higher interior point, and
the segment from the vertex to that point reaches the desired level.
-/

@[expose] public section

open Topology

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_interior_radialSlice {s : Set E} (convex : Convex ℝ s)
    (interior_nonempty : (interior s).Nonempty) (f : E →L[ℝ] ℝ) (x : E) (h : ℝ)
    (vertex : x ∈ s) (positive : 0 < h) (y : E) (hy : y ∈ s) (high : h < f (y - x)) :
    ∃ z, z ∈ radialSlice s f x h ∧ z ∈ interior s := by
  let H : Set E := {q | h < f (q - x)}
  have open_H : IsOpen H :=
    isOpen_lt continuous_const (f.continuous.comp (continuous_id.sub continuous_const))
  have dense : y ∈ closure (interior s) := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior interior_nonempty]
    exact subset_closure hy
  obtain ⟨q, q_high, q_inside⟩ :=
    mem_closure_iff_nhds.mp dense H (open_H.mem_nhds high)
  have height : h < f (q - x) := q_high
  have height_positive : 0 < f (q - x) := positive.trans height
  have parameter : h / f (q - x) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos positive height_positive,
      (div_lt_iff₀ height_positive).mpr (by simpa only [one_mul] using height)⟩
  let z := radialSlicePoint f x h q
  have inside : z ∈ interior s :=
    convex.openSegment_self_interior_subset_interior vertex q_inside
      (lineMap_mem_openSegment ℝ x q parameter)
  exact ⟨z, ⟨interior_subset inside, radialSlicePoint_level f x h q height_positive.ne'⟩, inside⟩

end Unfoldings
