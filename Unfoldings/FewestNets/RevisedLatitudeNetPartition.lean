module

public import Unfoldings.FewestNets.RevisedLatitudePlacement
public import Unfoldings.FewestNets.RevisedLatitudeSelectedRouting
public import Unfoldings.FewestNets.RevisedLatitudeSavedBank
public import Unfoldings.Development.NetPartition
public import Unfoldings.Roof.PolygonClippedModel

/-! The revised latitude construction partitions the original acute triangular surface into nets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets FewestNets.RevisedLatitudeGrid Cap Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P

set_option maxHeartbeats 3600000 in
/-- The actual revised annular label component unfolds into a single
nonoverlapping net with original-edge cuts. -/
theorem hasOriginalEdgeNet_of_revisedLatitude_annular_label {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
    (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
    (generic : ∀ f (i : ChordFace a) j, (LatitudeRings.chordBasis (rings_oriented positive small) i).coord j
      (placement (N.normal f)) ≠ 0)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (k : AnnularTriangle a) (seed : Face) (seed_label : label seed = .inr k) :
    C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  obtain ⟨D, bp, φ, σ, start, present, H, route, selected, component,
    φpos, φsmall, rad, reserve, _, span⟩ :=
    P.exists_revisedLatitude_annular_label_routing N positive small placement label
      chosen generic angles k seed seed_label
  let frame := (placement.trans (selectorFrame (.inr k))).trans (horizontalChartIsometry D.reorient)
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let region := latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
  let B := latitudeTriangleSideDirections (-D.halfBase) D.halfBase D.base D.apex D.height bp D.height_pos
  let compact := isCompact_latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
  obtain ⟨M⟩ := roof.exists_componentFiniteSlopeModel_of_polygon B compact present
    (Set.nonempty_of_mem (roof.seed_mem_selectionComponent region start))
  have pole_area (p : Plane) (hp : p ∈ region) (q : Plane) (hq : q ∈ region) :
      |orient 0 p q| / 2 ≤ (spacing a / (2 * 0.9612)) * ordinateBound a (isPolarStrip a k.1.val) := by
    have eq : orient 0 p q = p 0 * q 1 - q 0 * p 1 := by
      simp only [orient, PiLp.zero_apply, sub_zero]
      ring
    rw [eq]
    exact D.pole_triangle_bound hp hq
  have net := route.hasOriginalEdgeNet_of_signed_cellAllowance M selected φpos
    (by linarith only [φsmall, pi_gt_three]) rad pole_area reserve span
  exact component ▸ C.hasOriginalEdgeNet_of_restrictFaces _ _ net

/-- A convex polyhedron with a conforming triangular boundary mesh whose
corner angles are at most `π / 2 - a` partitions into fewer than `296 / a^4`
nonoverlapping nets along edges of the input triangles. -/
theorem exists_acute_netPartition_lt_296 {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∃ n : ℕ, (n : ℝ) < 296 / a ^ 4 ∧ C.HasNetPartition n := by
  classical
  let normals := P.supportingNormals
  obtain ⟨placement, label, chosen, generic, count⟩ :=
    P.exists_revisedLatitude_low_component_placement normals positive small angles
  refine ⟨_, count, C.hasNetPartition_card_labeledSeamGraph label ?_⟩
  intro c
  obtain ⟨seed, represented⟩ := c.exists_rep
  rw [← represented]
  cases label_eq : label seed with
  | inl pole =>
    exact P.hasOriginalEdgeNet_of_revisedLatitude_polar_label normals positive small placement label
      chosen generic pole angles seed label_eq
  | inr k =>
    exact P.hasOriginalEdgeNet_of_revisedLatitude_annular_label normals positive small placement label
      chosen generic angles k seed label_eq

end Unfoldings.SpatialFolding.ConvexBoundary
