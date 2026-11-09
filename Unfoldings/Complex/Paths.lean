module

public import Unfoldings.Complex
public import Unfoldings.Geometry.Paths
public import Unfoldings.Metric.Paths

/-!
# The triangle route metric is geodesic

Distance is the infimum of lengths of actual continuous paths. In each
finite-distance component that infimum is attained by a metric geodesic.
No development, embedding, or manifold hypothesis is needed.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The route distance agrees with continuous-path intrinsic distance on every cut realization. -/
theorem eDistance_eq_edist (retain : Set C.Seam) (x y : C.Realization retain) :
    Path.eDistance x y = edist x y :=
  MetricGluing.eDistance_eq_edist C.Cell (fun f => (C.triangle f).cellPath)
    (fun f a b => ((C.triangle f).eLength_cellPath a b).le) (C.glue retain) x y

/-- Every finite intrinsic distance is attained by an actual continuous metric geodesic. -/
theorem exists_geodesic (retain : Set C.Seam) (x y : C.Realization retain)
    (finite : edist x y ≠ ⊤) :
    ∃ p : Path x y, p.IsGeodesic :=
  MetricGluing.exists_geodesic C.Cell (fun f => (C.triangle f).cellPath)
    (fun f a b => ((C.triangle f).eLength_cellPath a b).le) (C.glue retain) x y finite

/-- A chosen geodesic; uniqueness and source-cut-locus properties are separate later results. -/
def geodesic (retain : Set C.Seam) (x y : C.Realization retain)
    (finite : edist x y ≠ ⊤) : Path x y :=
  Classical.choose (C.exists_geodesic retain x y finite)

theorem geodesic_isGeodesic (retain : Set C.Seam) (x y : C.Realization retain)
    (finite : edist x y ≠ ⊤) : (C.geodesic retain x y finite).IsGeodesic :=
  Classical.choose_spec (C.exists_geodesic retain x y finite)

end Unfoldings.TriangleComplex
