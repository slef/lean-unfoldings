module

public import Unfoldings.FewestNets.IcosahedronAdjacentFace
public import Unfoldings.Geometry.GnomonicRadius

/-! The two site comparisons along the rays of a Voronoi cell corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductGeometry Cap

/-- Slope of the neighboring dual vertex in the chart centered at the given facet. -/
def adjacentSlope {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) : Plane :=
  centeredSlope (facetNormal hq t) (facetNormal hq (adjacentFace hq t k))

/-- The signed support gap between two corners of the central facet at a slope. -/
def cornerGap {q : ℕ} (hq : 0 < q) (t : MeshFace q) (i j : Fin 3) : Plane →ₗ[ℝ] ℝ :=
  (innerSL ℝ (horizontal (northFrame (facetNormal hq t)
    (inscribedCorners t i - inscribedCorners t j)))).toLinearMap

theorem cornerGap_centeredSlope {q : ℕ} (hq : 0 < q) (t : MeshFace q) (i j : Fin 3)
    {x : Space} (unit : ‖x‖ = 1) (near : angle (facetNormal hq t) x < Real.pi / 2) :
    cornerGap hq t i j (centeredSlope (facetNormal hq t) x) =
      (northFrame (facetNormal hq t) x 2)⁻¹ *
      (inner ℝ x (inscribedCorners t i) - inner ℝ x (inscribedCorners t j)) := by
  let N := facetNormal hq t
  let d := inscribedCorners t i - inscribedCorners t j
  let z := centeredSlope N x
  have height : northFrame N d 2 = 0 := by
    rw [northFrame_height N (facetNormal_unit hq t)]
    change inner ℝ (facetNormal hq t) (inscribedCorners t i - inscribedCorners t j) = 0
    rw [inner_sub_right, inner_facetNormal, inner_facetNormal, meshGauge_corner, meshGauge_corner,
      sub_self]
  have value := inner_northLift_centeredSlope (facetNormal_unit hq t) unit near d
  change inner ℝ (northLift z) (northFrame N d) = _ at value
  rw [horizontal_inner, northLift_horizontal, height, mul_zero, add_zero, real_inner_comm] at value
  change inner ℝ (horizontal (northFrame N d)) z = _
  rw [value]
  dsimp only [d]
  rw [inner_sub_right]

theorem cornerGap_adjacentSlope_eq_zero {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) {i j k : Fin 3} (ik : i ≠ k) (jk : j ≠ k) :
    cornerGap hq t i j (adjacentSlope hq t k) = 0 := by
  let s := adjacentFace hq t k
  have ai := (corner_mem_adjacentFace_iff qbig hq t k i).mpr ik
  have aj := (corner_mem_adjacentFace_iff qbig hq t k j).mpr jk
  have eq := (inner_facetNormal_eq_iff_corner qbig hq s
    (siteOfCorner t i) (siteOfCorner t j) ai).mpr aj
  change inner ℝ (facetNormal hq s) (inscribedCorners t j) =
    inner ℝ (facetNormal hq s) (inscribedCorners t i) at eq
  rw [adjacentSlope, cornerGap_centeredSlope hq t i j (facetNormal_unit hq s)
    (facetNormal_angle_adjacent_lt qbig hq t k), eq, sub_self, mul_zero]

theorem cornerGap_adjacentSlope_pos {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) {i j : Fin 3} (ij : i ≠ j) :
    0 < cornerGap hq t i j (adjacentSlope hq t j) := by
  let s := adjacentFace hq t j
  have ai := (corner_mem_adjacentFace_iff qbig hq t j i).mpr ij
  have aj := (corner_mem_adjacentFace_iff qbig hq t j j).not.mpr (by simp)
  have gap : inner ℝ (facetNormal hq s) (inscribedCorners t j) <
      inner ℝ (facetNormal hq s) (inscribedCorners t i) :=
    lt_of_le_of_ne (bound_facetNormal_of_corner qbig hq s (siteOfCorner t i) ai (siteOfCorner t j))
      ((inner_facetNormal_eq_iff_corner qbig hq s (siteOfCorner t i)
        (siteOfCorner t j) ai).not.mpr aj)
  have short := facetNormal_angle_adjacent_lt qbig hq t j
  have unit := facetNormal_unit hq s
  rw [adjacentSlope, cornerGap_centeredSlope hq t i j unit short]
  exact mul_pos (inv_pos.mpr (centeredSlope_height_pos (facetNormal_unit hq t) unit short))
    (sub_pos.mpr gap)

theorem mem_closedMinorArc_adjacent_of_slope_segment {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (t : MeshFace q) (k : Fin 3) {x : Space} (unit : ‖x‖ = 1)
    (short : angle (facetNormal hq t) x < Real.pi / 2)
    (mem : centeredSlope (facetNormal hq t) x ∈ segment ℝ 0 (adjacentSlope hq t k)) :
    x ∈ closedMinorArc (facetNormal hq t) (facetNormal hq (adjacentFace hq t k)) := by
  let N := facetNormal hq t
  let L := northFrame N
  have mapped : L x ∈ gnomonicNormal '' segment ℝ 0 (adjacentSlope hq t k) :=
    ⟨_, mem, gnomonicNormal_centeredSlope (facetNormal_unit hq t) unit short⟩
  rw [gnomonicNormal_image_segment, gnomonicNormal_zero,
    ← northFrame_center N (facetNormal_unit hq t), adjacentSlope,
    gnomonicNormal_centeredSlope (facetNormal_unit hq t) (facetNormal_unit hq _)
      (facetNormal_angle_adjacent_lt qbig hq t k),
    ← SpatialRotation.image_closedMinorArc_linearIsometry] at mapped
  obtain ⟨w, hw, eq⟩ := mapped
  exact L.injective eq ▸ hw

end Unfoldings.FewestNets.Icosahedron
