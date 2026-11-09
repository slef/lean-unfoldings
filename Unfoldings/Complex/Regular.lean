module

public import Unfoldings.Metric.BallChart
public import Unfoldings.Complex.Charts
public import Unfoldings.Complex.HingeCharts
public import Unfoldings.Cone.FlatCharts
public import Unfoldings.Path.Continuation

/-!
# Actual regular points and unique geodesic continuation

Regularity means an isometry of whole metric balls with a Euclidean ball.
The preceding constructions prove it at face interiors, nonvertex retained
seams with distinct incident faces, and flat interior vertices. These charts
give uniqueness of geodesic continuation from an initial interval.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Regularity in the original intrinsic metric, using a genuine open
two-dimensional Euclidean ball. -/
def IsRegularPoint (retain : Set C.Seam) (x : C.Realization retain) : Prop :=
  HasMetricBallChart Plane x

theorem isRegularPoint_face (retain : Set C.Seam) (f : Face) (x : C.Cell f)
    (inside : x.val ∈ interior (C.triangle f).carrier) :
    C.IsRegularPoint retain (C.faceMap retain f x) := by
  obtain ⟨N⟩ := C.exists_faceChart retain f x inside
  exact ⟨N.radius, N.positive, x.val, ⟨N.chart.symm⟩⟩

theorem isRegularPoint_hinge (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) :
    C.IsRegularPoint retain
      (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x)) := by
  obtain ⟨N⟩ := C.exists_hingeChart retain s kept different x regular
  exact ⟨N.radius, N.positive, x.val, ⟨N.chart.symm⟩⟩

theorem geodesics_eq_of_initial_interval (retain : Set C.Seam)
    {a b c d : C.Realization retain} {p : Path a b} {q : Path c d}
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (initial : ∃ ε : unitInterval, 0 < ε ∧ ∀ t ≤ ε, p t = q t)
    (regular : ∀ t ∈ Set.Ioo (0 : unitInterval) 1, C.IsRegularPoint retain (p t)) :
    ∀ t, p t = q t := by
  apply geodesic.eq_of_initial_interval other initial (E := Plane)
  intro t ht
  obtain ⟨D, U, open_D, inside, _open_U, chart⟩ := (regular t ht).exists_open_chart
  exact ⟨D, U, open_D, inside, chart⟩

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem isRegularPoint_flat_vertex (interior : ¬ C.IsBoundaryVertex retain v)
    (flat : C.totalAngle retain v = 2 * Real.pi) :
    C.IsRegularPoint retain (C.vertexPoint retain v) := by
  obtain ⟨N⟩ := F.exists_flatVertexChart retain v interior flat
  refine ⟨N.radius, N.positive, (0 : Plane), ?_⟩
  have chart := Nonempty.intro N.chart.symm
  have balls : Metric.eball (0 : Plane) (ENNReal.ofReal N.radius) =
      Metric.ball (0 : Plane) N.radius := Metric.eball_ofReal
  rw [balls] at chart
  exact chart

end Unfoldings.SpatialFolding
