module

public import Unfoldings.Complex.SubdivisionMetric
public import Unfoldings.Complex.Regular
public import Unfoldings.Metric.BallChartTransport

/-! Refinement preserves intrinsic Euclidean regularity, including newly inserted vertices. -/

@[expose] public section

namespace Unfoldings.TriangleComplex.Subdivision.Conforming

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {S : C.Subdivision D} {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (H : S.Conforming retain fineRetain)

theorem isRegularPoint_iff (x : D.Realization fineRetain) :
    C.IsRegularPoint retain (H.metricEquiv x) ↔ D.IsRegularPoint fineRetain x :=
  hasMetricBallChart_isometryEquiv_iff H.metricEquiv x

end Unfoldings.TriangleComplex.Subdivision.Conforming
