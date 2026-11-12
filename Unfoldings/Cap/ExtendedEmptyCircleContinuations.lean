module

public import Unfoldings.Cap.ExtendedCalibratedComparisonArcs
public import Unfoldings.Cap.EmptyCircleContinuation

/-! Construct actual disappearing-strip continuations in the same roof calibration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

theorem cornerExtendedOutward_empty_circle_continuation (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {ε : ℝ} (error_bounds : ε ∈ Set.Ioc (0 : ℝ) (1 / 8)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ (D : FacewiseDevelopment L.partition.pairedComplex R.retain)
      (B : R.FiveSectorFrameData positive small (R.completedDevelopment D)),
      (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
        p - K.projectedVertex origin ∈ closedFiveSector t i →
        p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
        ε * ‖p - K.projectedVertex origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q (K.projectedVertex origin))).re ∧
        ε * ‖p - K.projectedVertex origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q (K.projectedVertex origin))).im) →
      L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi →
      ∀ (i : FiveSector) (S : MonotoneStrip),
      ∀ data : R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff,
        S.ApproachedPinchesIn
          (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
            Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
            (fiveSectorFrame t positive small i).place
              (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff →
        ∀ circle ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)),
          circle ∉ data.emptyCircleExceptions →
          data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = circle} = ∅ →
          (S.openSlab 0 cutoff).Nonempty →
          Nonempty (B.EmptyCircleContinuation i data (cutoff / 4) circle) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun D B face_bounds budget i S data pinches circle circle_bounds outside empty
    nonempty => ?_
  have cutoff_positive : 0 < cutoff := by
    by_contra nonpositive
    have bound := mul_nonpos_of_nonneg_of_nonpos error_bounds.1.le
      (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt nonpositive) (by norm_num : (0 : ℝ) ≤ 4))
    exact (not_lt_of_ge bound) (circle_bounds.1.trans circle_bounds.2)
  have physical_positive : 0 < cutoff / 4 := div_pos cutoff_positive (by norm_num)
  have small_error : ε < 1 / 2 := error_bounds.2.trans_lt (by norm_num)
  have physical_far : circle < (1 / 2 - ε) * (cutoff / 4) :=
    circle_bounds.2.trans (mul_lt_mul_of_pos_right (by linarith [error_bounds.2]) physical_positive)
  have far : circle < (1 / 2 - ε) * cutoff := physical_far.trans_le
    (mul_le_mul_of_nonneg_left (by linarith : cutoff / 4 ≤ cutoff) (by linarith))
  apply B.exists_emptyCircleContinuation i data pinches small_error circle_bounds.1 far
    physical_far outside empty nonempty
  intro w on_cut before target original near
  exact M.cornerExtendedOutward_proper_comparison_data positive small T internal source_height
    lower conforming height cutoff deep ε error_bounds.1.le D B face_bounds budget
    (cutoff / 4) (by linarith) w on_cut before target original circle near circle_bounds.2

end Unfoldings.ConvexCap.SectorForest
