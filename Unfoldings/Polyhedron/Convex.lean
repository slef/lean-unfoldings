module

public import Unfoldings.Complex.Folding
public import Unfoldings.Complex.Connectivity
public import Unfoldings.Metric.Connected
public import Unfoldings.Topology.ConvexBoundary

/-!
# Triangulated convex polyhedral boundaries

The body is the actual convex hull of the spatial triangle corners. The input
conditions say that the uncut complex embeds and covers exactly its frontier,
and that the body has spatial interior. No curvature, graph Euler formula,
shortest-path property or unfolding conclusion is included in these conditions.
Triangulation corners need not be extreme points or nonflat vertices.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- The convex hull of the spatial triangulation corners, including subdivision corners. -/
def vertexHull : Set Space :=
  convexHull ℝ (Set.range (fun p : Face × Fin 3 => F.place p.1 ((C.triangle p.1).vertex p.2)))

theorem convex_vertexHull : Convex ℝ F.vertexHull := convex_convexHull ℝ _

theorem compact_vertexHull : IsCompact F.vertexHull := (Set.finite_range _).isCompact_convexHull ℝ

theorem faceImage_subset_vertexHull (f : Face) : F.faceImage f ⊆ F.vertexHull := by
  rintro z ⟨x, hx, rfl⟩
  apply convexHull_min ?_ (F.convex_vertexHull.affine_preimage (F.place f).toAffineMap) hx
  rintro z ⟨i, rfl⟩
  exact subset_convexHull ℝ _ ⟨(f, i), rfl⟩

theorem surface_subset_vertexHull : F.surface ⊆ F.vertexHull :=
  Set.iUnion_subset F.faceImage_subset_vertexHull

/-- Geometric input conditions for a triangulation of a full-dimensional convex boundary. -/
structure ConvexBoundary : Prop where
  embedded : F.IsEmbedded
  interior_nonempty : (interior F.vertexHull).Nonempty
  boundary : F.surface = frontier F.vertexHull

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary)

include P

/-- The intrinsic realization is a topological sphere, derived from actual convexity. -/
def sphereHomeomorph : C.Realization Set.univ ≃ₜ Metric.sphere (0 : Space) 1 :=
  ((F.surfaceHomeomorph P.embedded).trans (Homeomorph.setCongr P.boundary)).trans
    (Classical.choice (F.convex_vertexHull.exists_homeomorph_frontier_sphere
      P.interior_nonempty F.compact_vertexHull.isBounded))

theorem connectedSpace : ConnectedSpace (C.Realization Set.univ) := by
  have dimension : 1 < Module.rank ℝ Space := by
    rw [← Module.finrank_eq_rank]
    norm_num [Space]
  let : ConnectedSpace (frontier F.vertexHull) := F.convex_vertexHull.frontier_connectedSpace
    P.interior_nonempty F.compact_vertexHull.isBounded dimension
  let h := (F.surfaceHomeomorph P.embedded).trans (Homeomorph.setCongr P.boundary)
  exact h.symm.surjective.connectedSpace h.symm.continuous

theorem edist_ne_top (x y : C.Realization Set.univ) : edist x y ≠ ⊤ := by
  let := P.connectedSpace
  exact edist_ne_top_of_preconnected x y

theorem duallyConnected : C.DuallyConnected Set.univ :=
  (C.duallyConnected_iff_edist_ne_top Set.univ).mpr P.edist_ne_top

/-- The ordinary intrinsic surface metric, with its original edistance and topology. -/
@[instance_reducible] def metricSpace : MetricSpace (C.Realization Set.univ) :=
  EMetricSpace.toMetricSpace P.edist_ne_top

theorem exists_geodesic (x y : C.Realization Set.univ) : ∃ p : Path x y, p.IsGeodesic :=
  C.exists_geodesic Set.univ x y (P.edist_ne_top x y)

end ConvexBoundary
end Unfoldings.SpatialFolding
