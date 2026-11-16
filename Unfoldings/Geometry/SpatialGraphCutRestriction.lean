module

public import Unfoldings.Geometry.SpatialGraphPartition
public import Unfoldings.Metric.PolygonalCutEqOn

/-! Changing cuts outside the actual graph patch preserves all original metric copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialGraphPartition

variable {height : Plane → ℝ} {region : Set Plane} {A : Type*}
  (P : SpatialGraphPartition height region A)

/-- Every physical patch point projects into its actual covered region. -/
theorem horizontal_mem_region (a : A) {p : Space} (member : p ∈ P.spatialCell a) :
    Cap.horizontal p ∈ region := by
  obtain ⟨q, ⟨z, hz, equal⟩, rfl⟩ := member
  have horizontal : Cap.horizontal ((P.plane a).place q) = z :=
    ((P.plane a).horizontal_place q).trans
      ((congrArg (P.plane a).project equal).symm.trans ((P.plane a).project.apply_symm_apply z))
  exact Eq.mpr (congrArg (fun x : Plane => x ∈ region) horizontal)
    (P.footprint_subset_region a hz)

variable [Finite A] (cuts other : Set Plane)
  (agree : ∀ p ∈ region, p ∈ cuts ↔ p ∈ other)

/-- Cuts agreeing on the actual covered patch preserve its entire intrinsic cut metric. -/
def cutEqOnEquiv : P.Cut cuts ≃ᵢ P.Cut other :=
  MetricGluing.polygonalCutEqOnEquiv P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) (Cap.horizontal ⁻¹' other)
    (fun a p hp => agree (Cap.horizontal p) (P.horizontal_mem_region a hp))

@[simp] theorem cutEqOnEquiv_liftCell (a : A) (p : P.footprint a) :
    P.cutEqOnEquiv cuts other agree (P.liftCell cuts a p) = P.liftCell other a p :=
  MetricGluing.polygonalCutEqOnEquiv_of _ _ _ _ _ _ _

theorem fold_cutEqOnEquiv (x : P.Cut cuts) :
    P.fold other (P.cutEqOnEquiv cuts other agree x) = P.fold cuts x :=
  MetricGluing.fold_polygonalCutEqOnEquiv _ _ _ _ _ x

end Unfoldings.SpatialGraphPartition
