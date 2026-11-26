module

public import Unfoldings.FewestNets.AcuteLatitudeSourceContour
public import Unfoldings.FewestNets.AcuteLatitudePlacement
public import Unfoldings.FewestNets.ThreeExitGraftFlatness
public import Unfoldings.Roof.PolygonClippedModel

/-! The latitude partition is a partition by nets on the original triangular mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets AcuteLatitudeGrid Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P

set_option maxHeartbeats 2800000 in
/-- Each annular label component admits a development along its original edges,
with no overlap of triangle interiors. -/
theorem hasOriginalEdgeNet_of_acuteLatitude_annular_label {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (placement : Space ≃ₗᵢ[ℝ] Space) (label : Face → Selector a)
    (chosen : ∀ f, placement (N.normal f) ∈ selectorSphere positive small (label f))
    (generic : ∀ f (i : ChordFace a) j, (chordBasis positive small i).coord j
      (placement (N.normal f)) ≠ 0)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a)
    (k : AnnularTriangle a) (seed : Face) (seed_label : label seed = .inr k) :
    C.HasOriginalEdgeNet ((C.labeledSeamGraph label).connectedComponentMk seed).supp := by
  obtain ⟨frame, left, right, base, apex, height, base_pos, height_pos,
    start, present, H, route, _, selected, component, area, radius_bound, span⟩ :=
    P.exists_acuteLatitude_annular_label_routing_selected N positive small placement label
      chosen generic angles k seed seed_label
  let normals := N.rotate frame
  let roof := (P.rotate frame).upperRoof normals
  let region := latitudeSlopeTriangle left right base apex height
  let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
  let compact := isCompact_latitudeSlopeTriangle left right base apex height
  obtain ⟨M⟩ := roof.exists_componentFiniteSlopeModel_of_polygon B compact present
    (Set.nonempty_of_mem (roof.seed_mem_selectionComponent region start))
  obtain ⟨level, S, ends, _, strict⟩ :=
    route.exists_acuteLatitude_sourceContour M positive small area radius_bound span
  let L := route.floorWindowModel level M S.higher
  have net := L.hasOriginalEdgeNet_of_complete_contour S selected ends strict
  exact component ▸ C.hasOriginalEdgeNet_of_restrictFaces _ _ net

/-- A convex polyhedron with a conforming triangular surface mesh of corner
angles at most `π / 2 - a` has a partition into fewer than `1440 / a^4`
original-edge nets. -/
theorem exists_acute_netPartition_lt_1440 {a : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∃ n : ℕ, (n : ℝ) < 1440 / a ^ 4 ∧ C.HasNetPartition n := by
  classical
  let normals := P.supportingNormals
  obtain ⟨placement, label, chosen, generic, count⟩ :=
    P.exists_acuteLatitude_low_component_placement normals positive small angles
  refine ⟨_, count, C.hasNetPartition_card_labeledSeamGraph label ?_⟩
  intro c
  obtain ⟨seed, represented⟩ := c.exists_rep
  rw [← represented]
  cases label_eq : label seed with
  | inl pole =>
    exact P.hasOriginalEdgeNet_of_acuteLatitude_polar_label normals positive small placement label
      chosen generic pole angles seed label_eq
  | inr k =>
    exact P.hasOriginalEdgeNet_of_acuteLatitude_annular_label normals positive small placement label
      chosen generic angles k seed label_eq

end Unfoldings.SpatialFolding.ConvexBoundary
