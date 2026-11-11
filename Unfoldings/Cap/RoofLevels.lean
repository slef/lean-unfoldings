module

public import Unfoldings.Cap.RoofExtension
public import Unfoldings.Cap.Boundary
public import Unfoldings.Geometry.ConvexSegmentExit

/-!
# The original footprint as an exact roof superlevel set

The supplied horizontal rim has zero roof height. If the cap has any positive
height, concavity forces strict negative height everywhere outside its original
footprint. The flat case is kept separate.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem face_height_nonneg (f : Face) (x : C.Cell f) : 0 ≤ K.folding.place f x.val 2 := by
  let height : Plane →ᵃ[ℝ] ℝ :=
    (EuclideanSpace.proj 2).toLinearMap.toAffineMap.comp (K.folding.place f).toAffineMap
  have convex : Convex ℝ {p | 0 ≤ height p} := (convex_Ici (0 : ℝ)).affine_preimage height
  have contained : (C.triangle f).carrier ⊆ {p | 0 ≤ height p} := by
    apply convexHull_min _ convex
    rintro p ⟨i, rfl⟩
    exact K.corners_above f i
  exact contained x.property

theorem roofHeight_nonneg_of_mem {p : Plane} (inside : p ∈ K.footprint) :
    0 ≤ K.roofHeight p := by
  obtain ⟨f, member⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset inside)
  rw [projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨x, carrier, rfl⟩ := member
  rw [K.roofHeight_face f ⟨x, carrier⟩]
  exact K.face_height_nonneg f ⟨x, carrier⟩

theorem roofHeight_eq_zero_of_frontier {p : Plane} (boundary : p ∈ frontier K.footprint) :
    K.roofHeight p = 0 := by
  have member : p ∈ K.footprint := K.compact_footprint.isClosed.closure_eq ▸ boundary.1
  obtain ⟨x, equal⟩ := K.toFootprint_surjective ⟨p, member⟩
  have projected : Cap.horizontal (K.folding.toSpace Set.univ x) = p := congrArg Subtype.val equal
  have bank := (K.projected_mem_frontier_iff_bankBoundary x).mp (projected ▸ boundary)
  have surface : K.folding.toSpace Set.univ x ∈ K.folding.surface :=
    (K.folding.range_toSpace Set.univ).subset ⟨x, rfl⟩
  have height := ((K.surface_iff_roofHeight _).mp surface).2
  rw [projected] at height
  rw [← height, K.height_eq_zero_of_bankBoundary x bank]

theorem mem_interior_of_positive_roofHeight {p : Plane} (member : p ∈ K.footprint)
    (positive : 0 < K.roofHeight p) : p ∈ interior K.footprint := by
  by_contra outside
  have zero := K.roofHeight_eq_zero_of_frontier
    ((mem_frontier_iff_notMem_interior member).mpr outside)
  linarith

/-- One positive-height point forces negative extension heights beyond the original rim. -/
theorem roofHeight_neg_outside {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {p : Plane} (outside : p ∉ K.footprint) :
    K.roofHeight p < 0 := by
  obtain ⟨t, bounds, boundary⟩ := exists_frontier_on_segment K.compact_footprint K.convex_projection
    (K.mem_interior_of_positive_roofHeight member positive) outside
  have concave := K.roofHeight_concave.2 (Set.mem_univ q) (Set.mem_univ p)
    (sub_nonneg.mpr bounds.2.le) bounds.1.le (show (1 - t) + t = 1 by ring)
  rw [← AffineMap.lineMap_apply_module q p t, K.roofHeight_eq_zero_of_frontier boundary] at concave
  change (1 - t) * K.roofHeight q + t * K.roofHeight p ≤ 0 at concave
  by_contra nonnegative
  have first := mul_pos (sub_pos.mpr bounds.2) positive
  have last := mul_nonneg bounds.1.le (le_of_not_gt nonnegative)
  linarith

/-- This excludes the globally flat roof explicitly: one positive-height point is sufficient. -/
theorem footprint_eq_roof_superlevel_zero {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) : K.footprint = {p | 0 ≤ K.roofHeight p} := by
  ext p
  constructor
  · exact K.roofHeight_nonneg_of_mem
  · intro nonnegative
    by_contra outside
    exact not_lt_of_ge nonnegative (K.roofHeight_neg_outside member positive outside)

end Unfoldings.ConvexCap
