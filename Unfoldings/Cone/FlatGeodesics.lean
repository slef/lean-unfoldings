module

public import Unfoldings.Cone.FlatCharts
public import Unfoldings.Path.ConvexChart
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Shortest paths at flat vertices

These results use the whole-ball isometry constructed from the actual
tangent fan. They construct geodesics, identify their Euclidean coordinates,
and give uniqueness among all ambient geodesics for endpoints sufficiently
close to the center.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex.FlatVertexChart

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} {v : C.Vertex retain} (N : C.FlatVertexChart retain v)
  {a b : C.Realization retain} {p q : Path a b}

theorem geodesic_coordinates (geodesic : p.IsGeodesic)
    (ha : a ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (hb : b ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (inside : ∀ t, p t ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (t : unitInterval) :
    (N.chart.symm ⟨p t, inside t⟩).val =
      AffineMap.lineMap (N.chart.symm ⟨a, ha⟩).val
        (N.chart.symm ⟨b, hb⟩).val (t : ℝ) :=
  geodesic.chart_eq_lineMap N.chart.symm ha hb inside t

/-- Every pair of points in the constructed chart is joined by an actual
ambient shortest path contained in that chart. -/
theorem exists_geodesic
    (ha : a ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius))
    (hb : b ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius)) :
    ∃ p : Path a b, p.IsGeodesic ∧
      ∀ t, p t ∈ Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal N.radius) := by
  apply Path.exists_geodesic_in_chart N.chart.symm _ ha hb
  rw [Metric.eball_ofReal]
  exact convex_ball _ _

/-- The endpoint margin forces every competing geodesic into the chart;
the uniqueness conclusion is in the whole surface. -/
theorem geodesic_unique (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (margin : edist a (C.vertexPoint retain v) + edist a b < ENNReal.ofReal N.radius) :
    p = q :=
  geodesic.eq_of_eball_chart other (C.vertexPoint retain v) (ENNReal.ofReal N.radius)
    N.chart.symm margin

end Unfoldings.TriangleComplex.FlatVertexChart
