module

public import Unfoldings.Roof.Boundary

public import Unfoldings.Roof.GnomonicArea
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The spherical normal polygon is the actual outward normal cone

At an interior roof vertex, no supporting normals are missing from the convex
hull of incident face normals in slope coordinates. A separating functional
would produce a nearby point of the cap contradicting its supporting inequality.
This identifies the geometric normal region without assuming strict curvature.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem supportHeight_eq_roof_of_mem_projectedTriangle (f : Face) {p : Plane}
    (present : p ∈ (K.projectedTriangle f).carrier) : K.supportHeight f p = K.roofHeight p := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at present
  obtain ⟨x, carrier, rfl⟩ := present
  exact (K.supportHeight_face f x).trans (K.roofHeight_face f ⟨x, carrier⟩).symm

theorem normalSlope_mem_normalPolygon_of_mem (v : C.Vertex Set.univ) (f : Face)
    (present : K.projectedVertex v ∈ (K.projectedTriangle f).carrier) :
    K.normalSlope f ∈ K.normalPolygon v := by
  obtain ⟨i, equal⟩ := K.projected_corner_of_vertex_mem v f present
  have vertex : C.vertexOfCorner Set.univ (f, i) = v := K.projectedVertex_injective equal
  exact subset_convexHull ℝ _ ⟨f, i, vertex, rfl⟩

/-- Local face incidence rules out any further supporting slope at an interior vertex. -/
theorem mem_normalPolygon_of_supports_footprint (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint) (g : Plane)
    (support : ∀ q ∈ K.footprint, K.roofHeight q ≤ K.roofHeight (K.projectedVertex v) -
      inner ℝ g (q - K.projectedVertex v)) : g ∈ K.normalPolygon v := by
  by_contra outside
  obtain ⟨functional, c, below, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (K.incidentSlopes v)) (K.compact_normalPolygon v).isClosed outside
  let direction : Plane := (InnerProductSpace.toDual ℝ Plane).symm functional
  have pairing (z : Plane) : inner ℝ z direction = functional z := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have star := eventually_piece_contains_center (fun f => (K.projectedTriangle f).carrier)
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed) (K.projectedVertex v)
  have near : {q | q ∈ K.footprint ∧ ∀ f, q ∈ (K.projectedTriangle f).carrier →
      K.projectedVertex v ∈ (K.projectedTriangle f).carrier} ∈ 𝓝 (K.projectedVertex v) := by
    filter_upwards [star, isOpen_interior.mem_nhds inside] with q incidence interior
    exact ⟨interior_subset interior, incidence⟩
  obtain ⟨t, positive, present, incidence⟩ :=
    exists_positive_ray_mem (K.projectedVertex v) direction _ near
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset present)
  have center := K.supportHeight_eq_roof_of_mem_projectedTriangle f (incidence f face)
  have endpoint := K.supportHeight_eq_roof_of_mem_projectedTriangle f face
  have ordered := support _ present
  rw [← endpoint, K.supportHeight_difference f (K.projectedVertex v)
      (K.projectedVertex v + t • direction), center, add_sub_cancel_left,
    inner_smul_right, inner_smul_right, pairing, pairing] at ordered
  have slope := below _ (K.normalSlope_mem_normalPolygon_of_mem v f (incidence f face))
  nlinarith

/-- The incident slope polygon is exactly the supporting-slope region over the footprint. -/
theorem mem_normalPolygon_iff_supports_footprint (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint) (g : Plane) :
    g ∈ K.normalPolygon v ↔ ∀ q ∈ K.footprint,
      K.roofHeight q ≤ K.roofHeight (K.projectedVertex v) -
        inner ℝ g (q - K.projectedVertex v) := by
  refine ⟨fun present q _ => K.normalPolygon_supports v present q,
    K.mem_normalPolygon_of_supports_footprint v inside g⟩

/-- The actual outward unit normals supporting the entire cap at this vertex. -/
def outwardNormalCone (v : C.Vertex Set.univ) : Set Space :=
  {n | ‖n‖ = 1 ∧ 0 < n 2 ∧ ∀ z ∈ K.folding.surface,
    inner ℝ n (z - K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)) ≤ 0}

/-- The normal image contains precisely all upward outward unit normals at an interior vertex. -/
theorem sphericalNormalPolygon_eq_outwardNormalCone (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint) :
    K.sphericalNormalPolygon v = K.outwardNormalCone v := by
  ext n
  constructor
  · intro present
    obtain ⟨unit, upward⟩ := K.sphericalNormalPolygon_unit present
    refine ⟨unit, upward, ?_⟩
    intro z surface
    obtain ⟨f, x, carrier, rfl⟩ := Set.mem_iUnion.mp surface
    exact K.sphericalNormalPolygon_supports present f ⟨x, carrier⟩
  · rintro ⟨unit, upward, support⟩
    let g : Plane := (n 2)⁻¹ • Cap.horizontal n
    refine ⟨g, K.mem_normalPolygon_of_supports_footprint v inside g ?_, ?_⟩
    · intro q present
      obtain ⟨z, surface, projection⟩ := present
      have vertex_surface : K.folding.toSpace Set.univ (C.vertexPoint Set.univ v) ∈
          K.folding.surface := (K.folding.range_toSpace Set.univ).subset ⟨_, rfl⟩
      have vertex_height := ((K.surface_iff_roofHeight _).mp vertex_surface).2
      have point_height := ((K.surface_iff_roofHeight _).mp surface).2
      have inequality := support z surface
      rw [Cap.horizontal_inner, map_sub] at inequality
      change inner ℝ (Cap.horizontal n) (Cap.horizontal z - K.projectedVertex v) +
        n 2 * (z 2 - K.folding.toSpace Set.univ (C.vertexPoint Set.univ v) 2) ≤ 0 at inequality
      have divided := mul_le_mul_of_nonneg_left inequality (inv_nonneg.mpr upward.le)
      rw [mul_zero, mul_add, ← mul_assoc, inv_mul_cancel₀ upward.ne', one_mul] at divided
      rw [point_height, vertex_height, projection] at divided
      change (n 2)⁻¹ * inner ℝ (Cap.horizontal n) (q - K.projectedVertex v) +
        (K.roofHeight q - K.roofHeight (K.projectedVertex v)) ≤ 0 at divided
      change K.roofHeight q ≤ K.roofHeight (K.projectedVertex v) -
        inner ℝ ((n 2)⁻¹ • Cap.horizontal n) (q - K.projectedVertex v)
      rw [real_inner_smul_left]
      linarith
    · exact Cap.gnomonicNormal_slope n unit upward

end Unfoldings.ConvexRoof
