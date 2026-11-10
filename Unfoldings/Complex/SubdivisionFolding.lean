module

public import Unfoldings.Complex.SubdivisionMetric
public import Unfoldings.Polyhedron.Convex

/-! Spatial foldings and convex boundary certificates survive conforming subdivisions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (F : SpatialFolding C) (S : C.Subdivision D)
  (H : S.Conforming Set.univ Set.univ)

/-- Restrict each spatial face motion to the actual child triangle. -/
def subdivide : SpatialFolding D where
  place g := (F.place (S.parent g)).comp (S.place g).toAffineIsometry
  joined s x := by
    have related := H.respects _ _ ⟨s, Set.mem_univ _, x, rfl, rfl⟩
    exact congrArg (F.toSpace Set.univ) ((C.point_eq_iff Set.univ _ _).mpr related)

@[simp] theorem subdivide_place (g : Child) (x : Plane) :
    (F.subdivide S H).place g x = F.place (S.parent g) (S.place g x) := rfl

/-- The spatial map commutes with the intrinsic subdivision equivalence for every cut system. -/
theorem subdivide_toSpace {retain : Set C.Seam} {fineRetain : Set D.Seam}
    (K : S.Conforming retain fineRetain) (x : D.Realization fineRetain) :
    (F.subdivide S H).toSpace fineRetain x = F.toSpace retain (K.metricEquiv x) := by
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue fineRetain) x
  rfl

theorem subdivide_embedded (embedded : F.IsEmbedded) : (F.subdivide S H).IsEmbedded := by
  intro x y equal
  apply H.metricEquiv.injective
  apply embedded
  simpa only [F.subdivide_toSpace S H H] using equal

theorem subdivide_surface : (F.subdivide S H).surface = F.surface := by
  rw [← (F.subdivide S H).range_toSpace Set.univ, ← F.range_toSpace Set.univ]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨H.metricEquiv x, (F.subdivide_toSpace S H H x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := H.metricEquiv.surjective x
    exact ⟨z, F.subdivide_toSpace S H H z⟩

/-- Adding points inside faces does not change the convex hull of the surface. -/
theorem vertexHull_eq_convexHull_surface : F.vertexHull = convexHull ℝ F.surface := by
  apply le_antisymm
  · apply convexHull_mono
    rintro y ⟨⟨f, i⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨f, _, (C.triangle f).vertex_mem i, rfl⟩
  · exact convexHull_min F.surface_subset_vertexHull F.convex_vertexHull

theorem subdivide_vertexHull : (F.subdivide S H).vertexHull = F.vertexHull := by
  rw [(F.subdivide S H).vertexHull_eq_convexHull_surface, F.subdivide_surface S H,
    F.vertexHull_eq_convexHull_surface]

theorem ConvexBoundary.subdivide (P : F.ConvexBoundary) : (F.subdivide S H).ConvexBoundary where
  embedded := F.subdivide_embedded S H P.embedded
  interior_nonempty := by
    rw [F.subdivide_vertexHull S H]
    exact P.interior_nonempty
  boundary := by rw [F.subdivide_surface S H, F.subdivide_vertexHull S H, P.boundary]

end Unfoldings.SpatialFolding
