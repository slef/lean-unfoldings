module

public import Unfoldings.Geometry.SpatialAffineGraph
public import Unfoldings.Geometry.GraphNormal

/-! Actual isometric coordinates and supporting normals for arbitrary affine roof planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- An affine height plane with rigid Euclidean coordinates and its actual upward unit normal. -/
structure SpatialPlane where
  height : Plane →ᵃ[ℝ] ℝ
  place : Plane →ᵃⁱ[ℝ] Space
  project : Plane ≃ᵃ[ℝ] Plane
  horizontal_place : ∀ x, Cap.horizontal (place x) = project x
  height_place : ∀ x, place x 2 = height (project x)
  normal : Space
  normal_unit : ‖normal‖ = 1
  normal_upward : 0 < normal 2
  normal_tangent : ∀ x, inner ℝ normal (place.linear x) = 0

namespace SpatialPlane

/-- The affine graph with intercept `c` and negative gradient `slope`. -/
def affineHeight (c : ℝ) (slope : Plane) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane c - (innerSL ℝ slope).toLinearMap.toAffineMap

@[simp] theorem affineHeight_apply (c : ℝ) (slope p : Plane) :
    affineHeight c slope p = c - inner ℝ slope p := rfl

/-- Construct an actual Euclidean support plane for any intercept and slope. -/
def ofGraph (c : ℝ) (slope : Plane) : SpatialPlane := by
  let data := exists_spatial_affine_graph (affineHeight c slope)
  let place := data.choose
  let project := data.choose_spec.choose
  have horizontal := data.choose_spec.choose_spec.1
  have vertical := data.choose_spec.choose_spec.2
  have constant (x : Plane) : inner ℝ (graphNormal slope) (place x) =
      (Real.sqrt (1 + ‖slope‖ ^ 2))⁻¹ * c := by
    rw [graphNormal_inner, horizontal, vertical, affineHeight_apply]
    ring
  exact {
    height := affineHeight c slope
    place := place
    project := project
    horizontal_place := horizontal
    height_place := vertical
    normal := graphNormal slope
    normal_unit := graphNormal_unit slope
    normal_upward := graphNormal_upward slope
    normal_tangent := fun x => by
      have chord := place.toAffineMap.linear_apply_vsub x 0
      change place.linear (x - 0) = place x - place 0 at chord
      rw [sub_zero] at chord
      rw [chord, inner_sub_right, constant, constant, sub_self] }

@[simp] theorem ofGraph_height (c : ℝ) (slope : Plane) :
    (ofGraph c slope).height = affineHeight c slope := rfl

@[simp] theorem ofGraph_normal (c : ℝ) (slope : Plane) :
    (ofGraph c slope).normal = graphNormal slope := rfl

/-- The normal equation recovers the stated affine height, everywhere in the plane. -/
theorem height_formula (P : SpatialPlane) (p : Plane) :
    P.height p = (inner ℝ P.normal (P.place 0) - inner ℝ (Cap.horizontal P.normal) p) /
      P.normal 2 := by
  let x := P.project.symm p
  have horizontal : Cap.horizontal (P.place x) = p :=
    (P.horizontal_place x).trans (P.project.apply_symm_apply p)
  have vertical : P.place x 2 = P.height p := by
    rw [P.height_place, P.project.apply_symm_apply]
  have chord := P.place.toAffineMap.linear_apply_vsub x 0
  change P.place.linear (x - 0) = P.place x - P.place 0 at chord
  rw [sub_zero] at chord
  have tangent := P.normal_tangent x
  rw [chord, inner_sub_right] at tangent
  have split := Cap.horizontal_inner P.normal (P.place x)
  rw [horizontal, vertical] at split
  apply (eq_div_iff P.normal_upward.ne').mpr
  linarith

/-- The stated upward normal supports exactly the subgraph of the stated affine height. -/
theorem supporting_iff (P : SpatialPlane) (z : Space) :
    inner ℝ P.normal (z - P.place 0) ≤ 0 ↔ z 2 ≤ P.height (Cap.horizontal z) := by
  rw [P.height_formula, le_div_iff₀ P.normal_upward, inner_sub_right]
  have split := Cap.horizontal_inner P.normal z
  constructor <;> intro order <;> linarith

end SpatialPlane
end Unfoldings
