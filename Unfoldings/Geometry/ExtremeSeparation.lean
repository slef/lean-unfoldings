module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Strict separating planes at finite-hull extreme points

An extreme point of a finite convex hull is outside the convex hull of the
remaining generators. That remaining hull is compact. Strict Hahn-Banach
separation gives a continuous linear functional positive on every nonzero
generator displacement from the extreme point.

This supplies a transverse level plane for constructing a vertex figure.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_strict_support_margin_of_finite_hull_extreme {s : Set E} (finite : s.Finite)
    {x : E} (extreme : x ∈ (convexHull ℝ s).extremePoints ℝ) :
    ∃ (f : E →L[ℝ] ℝ) (ε : ℝ), 0 < ε ∧ ∀ y ∈ s, y ≠ x → ε < f (y - x) := by
  have outside : x ∉ convexHull ℝ ((convexHull ℝ s) \ {x}) :=
    ((convex_convexHull ℝ s).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp extreme).2
  have inclusion : s \ {x} ⊆ (convexHull ℝ s) \ {x} :=
    fun _ hy => ⟨subset_convexHull ℝ s hy.1, hy.2⟩
  have not_mem : x ∉ convexHull ℝ (s \ {x}) :=
    fun member => outside (convexHull_mono inclusion member)
  have remaining : (s \ {x}).Finite := finite.subset Set.sdiff_subset
  obtain ⟨f, u, first, last⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (s \ {x})) (remaining.isCompact_convexHull ℝ).isClosed not_mem
  refine ⟨f, u - f x, sub_pos.mpr first, ?_⟩
  intro y hy different
  have in_remaining : y ∈ s \ {x} := ⟨hy, by simpa only [Set.mem_singleton_iff] using different⟩
  rw [map_sub]
  exact sub_lt_sub_right (last y (subset_convexHull ℝ _ in_remaining)) _

theorem exists_strict_support_of_finite_hull_extreme {s : Set E} (finite : s.Finite)
    {x : E} (extreme : x ∈ (convexHull ℝ s).extremePoints ℝ) :
    ∃ f : E →L[ℝ] ℝ, ∀ y ∈ s, y ≠ x → 0 < f (y - x) := by
  obtain ⟨f, ε, positive, supported⟩ :=
    exists_strict_support_margin_of_finite_hull_extreme finite extreme
  exact ⟨f, fun y hy different => positive.trans (supported y hy different)⟩

end Unfoldings
