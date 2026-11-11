module

public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Complex.InteriorCopyAngles
public import Unfoldings.Complex.CutEndpointBoundary
public import Unfoldings.Development.FlatDisk

/-!
# Developing cut disks while leaving flat subdivision vertices uncut

Only positive-curvature original vertices must meet cut seams. Every remaining
interior copy keeps its original full angle and has zero angular defect. This
removes the stronger requirement that all auxiliary vertices be cut.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  (retain : Set C.Seam)

include K in
/-- Cutting every positive-curvature endpoint leaves all actual interior vertex copies flat. -/
theorem interior_flat_of_curvature_cut
    (cut_curvature : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      ∃ s b, s ∉ retain ∧ v = C.seamVertex s b)
    (w : C.Vertex retain) (internal : ¬ C.IsBoundaryVertex retain w) :
    C.totalAngle retain w = 2 * Real.pi := by
  classical
  let inclusion := Set.subset_univ retain
  let v := C.vertexForgetCuts inclusion w
  have old_internal : ¬ C.IsBoundaryVertex Set.univ v := by
    intro boundary
    have present := (C.vertexPoint_mem_bankBoundary_iff Set.univ v).mpr boundary
    have preimage : C.vertexPoint retain w ∈ C.bankBoundary retain :=
      C.bankBoundary_preimage_forgetCuts inclusion (by
        change C.forgetCuts inclusion (C.vertexPoint retain w) ∈ C.bankBoundary Set.univ
        rw [← C.vertexPoint_vertexForgetCuts]
        exact present)
    exact internal ((C.vertexPoint_mem_bankBoundary_iff retain w).mp preimage)
  have not_positive : ¬ 0 < C.interiorAngularDefect Set.univ v := by
    intro positive
    obtain ⟨s, b, cut, endpoint⟩ := cut_curvature v positive
    exact internal (C.isBoundaryVertex_of_cut_endpoint retain w s cut b endpoint)
  have zero : C.interiorAngularDefect Set.univ v = 0 :=
    le_antisymm (not_lt.mp not_positive) (K.interiorCurvature_nonneg v)
  rw [TriangleComplex.interiorAngularDefect, ite_eq_right old_internal] at zero
  have angle : C.totalAngle Set.univ v = 2 * Real.pi := by linarith
  exact (C.totalAngle_eq_of_internal_copy inclusion w internal).trans angle

include K in
/-- A curvature-cut disk develops locally isometrically even with flat vertices in its interior. -/
theorem exists_development_of_curvature_cut_disk
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (cut_curvature : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      ∃ s b, s ∉ retain ∧ v = C.seamVertex s b) :
    ∃ E : FacewiseDevelopment C retain, ∀ x, ‖(disk x).val‖ < 1 → ∃ r > 0,
      Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  K.folding.exists_locally_isometric_development_of_flat_disk retain disk
    (K.interior_flat_of_curvature_cut retain cut_curvature)

end Unfoldings.ConvexCap
