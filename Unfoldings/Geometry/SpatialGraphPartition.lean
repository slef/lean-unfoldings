module

public import Unfoldings.Geometry.SupportedPlane
public import Unfoldings.Metric.PolygonalCut

/-! Actual finite rigid cell partitions of a prescribed spatial graph over a planar region. -/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u

/-- Actual rigid planar cells covering a graph patch. Different partitions may use different
support families; only their physical graph over the common region must agree. -/
structure SpatialGraphPartition (height : Plane → ℝ) (region : Set Plane) (A : Type u) where
  footprint : A → Set Plane
  plane : A → SpatialPlane
  closed : ∀ a, IsClosed (footprint a)
  convex : ∀ a, Convex ℝ (footprint a)
  full : ∀ a, (interior (footprint a)).Nonempty
  disjoint : ∀ a b, a ≠ b → Disjoint (interior (footprint a)) (interior (footprint b))
  cover : region = ⋃ a, footprint a
  active : ∀ a p, p ∈ footprint a → height p = (plane a).height p

namespace SpatialGraphPartition

variable {height : Plane → ℝ} {region : Set Plane} {A : Type u}
  (P : SpatialGraphPartition height region A)

theorem footprint_subset_region (a : A) : P.footprint a ⊆ region :=
  MetricGluing.cell_subset_of_cover P.footprint P.cover a

/-- Original rigid planar coordinates of one complete physical patch cell. -/
def planarCell (a : A) : Set Plane := (P.plane a).project.symm '' P.footprint a

def spatialCell (a : A) : Set Space := (P.plane a).place '' P.planarCell a

theorem isClosed_planarCell (a : A) : IsClosed (P.planarCell a) :=
  (P.plane a).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _ (P.closed a)

theorem isClosed_spatialCell (a : A) : IsClosed (P.spatialCell a) :=
  (P.plane a).place.isometry.isClosedEmbedding.isClosedMap _ (P.isClosed_planarCell a)

theorem convex_planarCell (a : A) : Convex ℝ (P.planarCell a) :=
  (P.convex a).affine_image (P.plane a).project.symm.toAffineMap

/-- Every original cell uses the specified graph height at its exact physical point. -/
theorem place_eq_graph (a : A) (p : P.footprint a) :
    (P.plane a).place ((P.plane a).project.symm p.val) =
      Cap.horizontalAtHeight p.val (height p.val) := by
  have horizontal := ((P.plane a).horizontal_place _).trans
    ((P.plane a).project.apply_symm_apply p.val)
  have vertical : (P.plane a).place ((P.plane a).project.symm p.val) 2 = height p.val := by
    rw [(P.plane a).height_place, (P.plane a).project.apply_symm_apply]
    exact (P.active a p.val p.property).symm
  ext j
  fin_cases j
  · exact congrArg (fun z : Plane => z 0) horizontal
  · exact congrArg (fun z : Plane => z 1) horizontal
  · exact vertical

variable [Finite A]

/-- The actual intrinsic cut of the entire graph patch, including all original bank copies. -/
abbrev Cut (cuts : Set Plane) := MetricGluing.PolygonalCut P.spatialCell P.isClosed_spatialCell
  (Cap.horizontal ⁻¹' cuts)

/-- The original spatial point of a cut copy. -/
def fold (cuts : Set Plane) : P.Cut cuts → Space :=
  (MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)).fold

/-- Lift a specified actual cell copy, without identifying other coincident cut-bank copies. -/
def liftCell (cuts : Set Plane) (a : A) (p : P.footprint a) : P.Cut cuts :=
  MetricGluing.of (fun a => P.spatialCell a)
    (MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts)).relation a
    ⟨(P.plane a).place ((P.plane a).project.symm p.val),
      (P.plane a).project.symm p.val, ⟨p.val, p.property, rfl⟩, rfl⟩

@[simp] theorem fold_liftCell (cuts : Set Plane) (a : A) (p : P.footprint a) :
    P.fold cuts (P.liftCell cuts a p) = Cap.horizontalAtHeight p.val (height p.val) :=
  P.place_eq_graph a p

theorem cut_complete (cuts : Set Plane) : CompleteSpace (P.Cut cuts) :=
  (MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts)).completeSpace_realization P.isClosed_spatialCell

end SpatialGraphPartition
end Unfoldings
