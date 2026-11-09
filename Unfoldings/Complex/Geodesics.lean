module

public import Unfoldings.Complex.Folding
public import Unfoldings.Path.Straight
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.Order.Compact

/-!
# Geodesics on spatially embedded triangle complexes

An embedded face is geodesically convex: a shortest path cannot leave it and
return. Its spatial trace between two face points is the straight segment.
Convexity of the whole surface is not needed for this individual-face result.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The parameters at which a path visits a given closed original face. -/
def faceTimes {a b : C.Realization Set.univ} (p : Path a b) (f : Face) : Set unitInterval :=
  p ⁻¹' Set.range (C.faceMap Set.univ f)

theorem isClosed_faceTimes {a b : C.Realization Set.univ} (p : Path a b) (f : Face) :
    IsClosed (C.faceTimes p f) :=
  (isCompact_range (C.faceMap_lipschitz Set.univ f).continuous).isClosed.preimage p.continuous

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem convex_faceImage (f : Face) : Convex ℝ (F.faceImage f) :=
  (C.triangle f).convex_carrier.affine_image (F.place f).toAffineMap

/-- A shortest path with two points in one face develops straight between them in space. -/
theorem geodesic_mem_spatial_segment {a b : C.Realization Set.univ} {p : Path a b}
    (geodesic : p.IsGeodesic) {s u t : unitInterval} (first : s ≤ u) (last : u ≤ t)
    (f : Face) (x y : C.Cell f) (start : p s = C.faceMap Set.univ f x)
    (finish : p t = C.faceMap Set.univ f y) :
    F.toSpace Set.univ (p u) ∈ segment ℝ (F.place f x.val) (F.place f y.val) := by
  have saturated : edist (F.toSpace Set.univ (p s)) (F.toSpace Set.univ (p t)) =
      edist (p s) (p t) := by
    rw [start, finish, F.toSpace_faceMap, F.toSpace_faceMap]
    exact (F.face_isometry f x y).trans ((F.faceMap_isometry Set.univ f x y).symm)
  simpa only [start, finish, F.toSpace_faceMap] using
    geodesic.map_mem_segment (F.toSpace Set.univ) (F.toSpace_lipschitz Set.univ)
      first last saturated

/-- On an embedded surface the original face is geodesically convex. -/
theorem geodesic_mem_face (embedded : F.IsEmbedded)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    {s u t : unitInterval} (first : s ≤ u) (last : u ≤ t)
    (f : Face) (x y : C.Cell f) (start : p s = C.faceMap Set.univ f x)
    (finish : p t = C.faceMap Set.univ f y) :
    p u ∈ Set.range (C.faceMap Set.univ f) := by
  have between := F.geodesic_mem_spatial_segment geodesic first last f x y start finish
  have inside : F.toSpace Set.univ (p u) ∈ F.faceImage f :=
    (F.convex_faceImage f).segment_subset ⟨x.val, x.property, rfl⟩
      ⟨y.val, y.property, rfl⟩ between
  obtain ⟨z, hz, equal⟩ := inside
  exact ⟨⟨z, hz⟩, embedded equal⟩

/-- The parameter set in a fixed closed face contains every interval between its points. -/
theorem geodesic_face_interval (embedded : F.IsEmbedded)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (f : Face) {s u t : unitInterval} (first : s ≤ u) (last : u ≤ t)
    (start : p s ∈ Set.range (C.faceMap Set.univ f))
    (finish : p t ∈ Set.range (C.faceMap Set.univ f)) :
    p u ∈ Set.range (C.faceMap Set.univ f) := by
  obtain ⟨x, hx⟩ := start
  obtain ⟨y, hy⟩ := finish
  exact F.geodesic_mem_face embedded geodesic first last f x y hx.symm hy.symm

theorem ordConnected_faceTimes (embedded : F.IsEmbedded)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic) (f : Face) :
    Set.OrdConnected (C.faceTimes p f) := by
  constructor
  intro s hs t ht u hu
  exact F.geodesic_face_interval embedded geodesic f hu.1 hu.2 hs ht

/-- Every visited face occupies one closed parameter interval, possibly a singleton. -/
theorem faceTimes_eq_Icc (embedded : F.IsEmbedded)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (f : Face) (visited : (C.faceTimes p f).Nonempty) :
    ∃ s t : unitInterval, s ≤ t ∧ C.faceTimes p f = Set.Icc s t := by
  obtain ⟨s, hs⟩ := (C.isClosed_faceTimes p f).isCompact.exists_isLeast visited
  obtain ⟨t, ht⟩ := (C.isClosed_faceTimes p f).isCompact.exists_isGreatest visited
  refine ⟨s, t, hs.2 ht.1, ?_⟩
  ext u
  exact ⟨fun hu => ⟨hs.2 hu, ht.2 hu⟩,
    fun hu => (F.ordConnected_faceTimes embedded geodesic f).out hs.1 ht.1 hu⟩

end Unfoldings.SpatialFolding
