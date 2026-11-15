module

public import Unfoldings.Metric.PhysicalCutRefinementEquiv
public import Unfoldings.Metric.FlatPhysicalCutCover

/-! Actual rigid planar parent pieces supply all metric data for a spatial cut refinement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E F I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [Finite I] [Finite J]
  (coarse : I → Set F) (fine : J → Set F) (closed : ∀ j, IsClosed (fine j)) (cuts : Set F)

/-- Rigid planar subdivision geometry constructs an exact spatial cut refinement.
Full dimension is required only in the original plane coordinates, allowing actual
polyhedral faces with empty ambient three-dimensional interiors. -/
def flatPhysicalCutRefinement (parent : J → I) (frame : I → E → F)
    (isometric : ∀ i, Isometry (frame i)) (region : I → Set E)
    (pieces : ∀ i, {j // parent j = i} → Set E)
    (closed_pieces : ∀ i j, IsClosed (pieces i j))
    (convex_pieces : ∀ i j, Convex ℝ (pieces i j))
    (full : ∀ i j, (interior (pieces i j)).Nonempty)
    (convex_region : ∀ i, Convex ℝ (region i))
    (region_cover : ∀ i, region i = ⋃ j, pieces i j)
    (parent_image : ∀ i, frame i '' region i = coarse i)
    (piece_images : ∀ i j, frame i '' pieces i j = fine j.val)
    (cut_closed : ∀ i, IsClosed (frame i ⁻¹' cuts))
    (outside : ∀ i, Disjoint (interior (region i)) (frame i ⁻¹' cuts)) :
    PhysicalCutRefinement coarse fine closed cuts := by
  have cover : ∀ i, coarse i = ⋃ j : {j // parent j = i}, fine j.val := by
    intro i
    rw [← parent_image i, region_cover i, Set.image_iUnion]
    simp only [piece_images i]
  refine ⟨parent, ?_, cover, ?_⟩
  · intro j z member
    exact Eq.mpr (congrArg (fun s : Set F => z ∈ s) (cover (parent j)))
      (Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, member⟩)
  · intro i
    apply cut_fold_isometry_of_isometric_images (pieces i) (closed_pieces i) (frame i)
      (isometric i) (fun j : {j // parent j = i} => fine j.val) (fun j => closed j.val)
      (piece_images i) cuts
    exact cut_fold_isometry_of_boundary_cuts (pieces i) (closed_pieces i) (frame i) cuts
      (convex_pieces i) (full i) (region_cover i) (convex_region i) (cut_closed i) (outside i)

end Unfoldings.MetricGluing
