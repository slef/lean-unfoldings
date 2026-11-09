module

public import Unfoldings.Source.AmbientCoordinates
public import Unfoldings.Source.FaceAtlas
public import Unfoldings.Complex.HingeCharts
public import Unfoldings.Metric.LocalRigidMap

/-!
# Actual source coordinates in an outward hinge chart

At a retained nonvertex seam point, the constructed hinge chart and the
constructed source-isometry neighborhood determine one rigid motion on
both incident faces. Thus their actual coordinate maps use the outward
hinge model, with the faces on opposite sides of their shared edge.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_source_hinge_placement :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (s : C.Seam)
      (q : (C.triangle (C.left s).face).Edge (C.left s).edge),
      ¬ (C.triangle (C.left s).face).IsVertex q →
        MetricGluing.point C.Cell (C.glue Set.univ) (C.edgePoint (C.left s) q) ∉
          sourceCutLocus source →
        ∃ δ > 0, ∃ A : Plane ≃ᵃⁱ[ℝ] Plane, ∀ a : C.Total,
          (a.1 = (C.left s).face ∨ a.1 = (C.right s).face) →
          dist (C.hingeCoordinates s a) q.val < δ →
          MetricGluing.point C.Cell (C.glue Set.univ) a ∉ sourceCutLocus source ∧
          P.extendedSourceCoordinates R (MetricGluing.point C.Cell (C.glue Set.univ) a) =
            A (C.hingeCoordinates s a) := by
  let := P.metricSpace
  intro source R s q regular outside
  let center := MetricGluing.point C.Cell (C.glue Set.univ) (C.edgePoint (C.left s) q)
  let H := C.hingeChart Set.univ s (Set.mem_univ s) (F.incident_faces_ne s) q regular
  obtain ⟨S, open_S, in_S, outside_S, isometry⟩ :=
    P.source_isometry_ambient_neighborhood R ⟨center, outside⟩
  have in_D : center ∈ Metric.eball center (ENNReal.ofReal H.radius) := by
    change edist center center < ENNReal.ofReal H.radius
    rw [edist_self]
    exact ENNReal.ofReal_pos.mpr H.positive
  obtain ⟨r, positive_r, in_domain, in_isometry, A, agrees⟩ :=
    exists_rigid_map_in_chart H.chart.symm Metric.isOpen_eball Metric.isOpen_ball
      (P.extendedSourceCoordinates R) open_S isometry center in_D in_S
  let δ := min r H.radius
  refine ⟨δ, lt_min positive_r H.positive, A, ?_⟩
  intro a faces close
  have extended_bound := C.edist_center_le_hingeCoordinates Set.univ s (Set.mem_univ s)
    (F.incident_faces_ne s) q a faces
  have distance_bound : dist (MetricGluing.point C.Cell (C.glue Set.univ) a) center ≤
      dist (C.hingeCoordinates s a) q.val := by
    have bound := ENNReal.toReal_mono (_root_.edist_ne_top _ _) extended_bound
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, dist_comm] using bound
  have near : MetricGluing.point C.Cell (C.glue Set.univ) a ∈ Metric.ball center r :=
    distance_bound.trans_lt (close.trans_le (min_le_left _ _))
  have coordinate_near : C.hingeCoordinates s a ∈ Metric.ball q.val H.radius :=
    close.trans_le (min_le_right _ _)
  have same : H.chart ⟨C.hingeCoordinates s a, coordinate_near⟩ =
      ⟨MetricGluing.point C.Cell (C.glue Set.univ) a, in_domain near⟩ :=
    Subtype.ext (H.agrees a faces coordinate_near)
  have inverse : (H.chart.symm
      ⟨MetricGluing.point C.Cell (C.glue Set.univ) a, in_domain near⟩).val =
        C.hingeCoordinates s a := by
    rw [← same, H.chart.symm_apply_apply]
  refine ⟨outside_S (in_isometry near), ?_⟩
  exact (agrees ⟨_, near⟩).symm.trans (congrArg A inverse)

end Unfoldings.SpatialFolding.ConvexBoundary
