module

public import Unfoldings.Cap.CurvaturePrunedDevelopment
public import Unfoldings.Development.RegularInteriorContact

/-! Pruned cap interior points have unique developed preimages, including boundary copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

open Classical in
theorem curved_regular_interior (x : C.Realization M.curvedRetain)
    (inside : ‖(M.curvedCutDisk x).val‖ < 1) : C.IsRegularPoint M.curvedRetain x :=
  K.folding.isRegularPoint_of_flat_disk M.curvedRetain M.curvedCutDisk
    (K.interior_flat_of_curvature_cut M.curvedRetain M.curved_cut_curvature) x inside

open Classical in
theorem curved_interior_contact_eq (E : FacewiseDevelopment C M.curvedRetain)
    (nonoverlap : E.Nonoverlapping) (x : C.Realization M.curvedRetain)
    (inside : ‖(M.curvedCutDisk x).val‖ < 1)
    (local_isometry : ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val))
    (y : C.Realization M.curvedRetain) (same : E.toPlane y = E.toPlane x) : x = y := by
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.curvedRetain) :=
    M.curvedCutDisk.symm.surjective.denseRange.preconnectedSpace M.curvedCutDisk.symm.continuous
  exact FacewiseDevelopment.Nonoverlapping.eq_of_toPlane_eq_at_regular_local_isometry E nonoverlap
    x (M.curved_regular_interior x inside) local_isometry y same

open Classical in
theorem curved_injective_iff_boundary_injective (E : FacewiseDevelopment C M.curvedRetain)
    (nonoverlap : E.Nonoverlapping)
    (local_isometry : ∀ x, ‖(M.curvedCutDisk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val)) :
    Function.Injective E.toPlane ↔ Set.InjOn E.toPlane (C.bankBoundary M.curvedRetain) := by
  refine ⟨fun injective => injective.injOn, ?_⟩
  intro boundary_injective x y same
  have inside_of_nonboundary (z : C.Realization M.curvedRetain)
      (outside : z ∉ C.bankBoundary M.curvedRetain) : ‖(M.curvedCutDisk z).val‖ < 1 := by
    have at_most : ‖(M.curvedCutDisk z).val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (M.curvedCutDisk z).property
    apply lt_of_le_of_ne at_most
    intro equal
    exact outside ((K.folding.bankBoundary_iff_disk_norm_eq_one M.curvedRetain
      M.curvedCutDisk z).mpr equal)
  by_cases first : x ∈ C.bankBoundary M.curvedRetain
  · by_cases last : y ∈ C.bankBoundary M.curvedRetain
    · exact boundary_injective first last same
    · have inside := inside_of_nonboundary y last
      exact (M.curved_interior_contact_eq E nonoverlap y inside
        (local_isometry y inside) x same).symm
  · have inside := inside_of_nonboundary x first
    exact M.curved_interior_contact_eq E nonoverlap x inside
      (local_isometry x inside) y same.symm

end Unfoldings.ConvexCap.SectorForest
