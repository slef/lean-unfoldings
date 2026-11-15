module

public import Unfoldings.Geometry.SpatialEnvelopeWholeSurface
public import Unfoldings.Metric.PolygonalClosedCover
public import Unfoldings.Metric.Connected
public import Mathlib.Analysis.Convex.Contractible

/-! A complete intrinsic polyhedral metric plane on the entire actual finite supported roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

theorem wholeSurface_complete : CompleteSpace (PolygonalPoint (wholeSurface family)) :=
  PolygonalPoint.completeSpace_of_finite_closed_cover (wholeCell family)
    (isClosed_wholeCell family) (convex_wholeCell family) (wholeSurface_eq_iUnion_cells family)

/-- The intrinsic metric retains the original full spatial graph topology at all crease points. -/
def wholeSurfaceIntrinsicHomeomorph : PolygonalPoint (wholeSurface family) ≃ₜ wholeSurface family :=
  PolygonalPoint.closedCoverHomeomorph (wholeCell family) (isClosed_wholeCell family)
    (convex_wholeCell family) (wholeSurface_eq_iUnion_cells family)

/-- This is the whole unbounded metric roof, with a constructed plane topology. -/
def wholeSurfacePlaneHomeomorph : PolygonalPoint (wholeSurface family) ≃ₜ Plane :=
  (wholeSurfaceIntrinsicHomeomorph family).trans (wholeSurfaceHomeomorph family)

theorem wholeSurface_contractible : ContractibleSpace (PolygonalPoint (wholeSurface family)) :=
  (wholeSurfacePlaneHomeomorph family).contractibleSpace

theorem wholeSurface_edist_ne_top (x y : PolygonalPoint (wholeSurface family)) : edist x y ≠ ⊤ := by
  let : ContractibleSpace (PolygonalPoint (wholeSurface family)) := wholeSurface_contractible family
  exact edist_ne_top_of_preconnected x y

/-- The whole physical roof has a genuine metric, not an extended-distance certificate. -/
@[instance_reducible] def wholeSurfaceMetricSpace :
    MetricSpace (PolygonalPoint (wholeSurface family)) :=
  EMetricSpace.toMetricSpace (wholeSurface_edist_ne_top family)

end Unfoldings.SpatialEnvelope
