module

public import Unfoldings.Geometry.ExtremeSeparation

/-!
# Constructed transverse radial slices

A positive level of a strict supporting functional gives a genuine affine
section of the convex body. Every other finite-hull generator projects along
its original vertex ray to this section. A uniform separating margin places
all these projected points inside their original body segments.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialSlice (s : Set E) (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) : Set E :=
  s ∩ {z | f (z - x) = h}

def radialSlicePoint (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) (y : E) : E :=
  AffineMap.lineMap x y (h / f (y - x))

theorem radialSlicePoint_level (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) (y : E)
    (nonzero : f (y - x) ≠ 0) : f (radialSlicePoint f x h y - x) = h := by
  rw [radialSlicePoint, AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  exact div_mul_cancel₀ h nonzero

theorem radialSlicePoint_mem_segment (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) (y : E)
    (positive : 0 < f (y - x)) (level_nonnegative : 0 ≤ h) (level_le : h ≤ f (y - x)) :
    radialSlicePoint f x h y ∈ segment ℝ x y := by
  apply lineMap_mem_segment
  exact ⟨div_nonneg level_nonnegative positive.le,
    (div_le_iff₀ positive).mpr (by simpa only [one_mul] using level_le)⟩

theorem radialSlicePoint_ne_origin (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) (y : E)
    (nonzero : f (y - x) ≠ 0) (level_positive : 0 < h) : radialSlicePoint f x h y ≠ x := by
  intro equal
  have height := radialSlicePoint_level f x h y nonzero
  rw [equal, sub_self, map_zero] at height
  exact level_positive.ne' height.symm

theorem convex_radialSlice {s : Set E} (convex : Convex ℝ s)
    (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) : Convex ℝ (radialSlice s f x h) := by
  have hyperplane : {z | f (z - x) = h} = f ⁻¹' {f x + h} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, map_sub]
    constructor <;> intro equal <;> linarith
  rw [radialSlice, hyperplane]
  exact convex.inter ((convex_singleton (f x + h)).linear_preimage f.toLinearMap)

theorem isCompact_radialSlice {s : Set E} (compact : IsCompact s)
    (f : E →L[ℝ] ℝ) (x : E) (h : ℝ) : IsCompact (radialSlice s f x h) :=
  compact.inter_right (isClosed_eq (f.continuous.comp (continuous_id.sub continuous_const))
    continuous_const)

theorem radialSlicePoint_mem {s : Set E} (convex : Convex ℝ s) (f : E →L[ℝ] ℝ)
    (x : E) (h : ℝ) (y : E) (hx : x ∈ s) (hy : y ∈ s)
    (positive : 0 < f (y - x)) (level_nonnegative : 0 ≤ h) (level_le : h ≤ f (y - x)) :
    radialSlicePoint f x h y ∈ radialSlice s f x h :=
  ⟨convex.segment_subset hx hy
    (radialSlicePoint_mem_segment f x h y positive level_nonnegative level_le),
    radialSlicePoint_level f x h y positive.ne'⟩

/-- Construct a positive transverse body section and the projected points of
every other generator, without assuming a vertex-figure polygon as input. -/
theorem exists_radialSlice_of_finite_hull_extreme {s : Set E} (finite : s.Finite)
    {x : E} (extreme : x ∈ (convexHull ℝ s).extremePoints ℝ) :
    ∃ (f : E →L[ℝ] ℝ) (h : ℝ), 0 < h ∧
      ∀ y ∈ s, y ≠ x → h < f (y - x) ∧
        radialSlicePoint f x h y ∈ radialSlice (convexHull ℝ s) f x h := by
  obtain ⟨f, h, positive, supported⟩ :=
    exists_strict_support_margin_of_finite_hull_extreme finite extreme
  refine ⟨f, h, positive, ?_⟩
  intro y hy different
  have bound := supported y hy different
  exact ⟨bound, radialSlicePoint_mem (convex_convexHull ℝ s) f x h y
    extreme.1 (subset_convexHull ℝ s hy) (positive.trans bound) positive.le bound.le⟩

end Unfoldings
