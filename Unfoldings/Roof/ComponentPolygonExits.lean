module

public import Unfoldings.Convex.PolygonSideDirections
public import Unfoldings.Roof.ComponentClippedExtension
public import Unfoldings.Roof.SelectionBoundaryContacts
public import Unfoldings.Roof.VertexProgress

/-! Every actual frontier vertex can leave along a consistently assigned support side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {slopes : Set Plane} (seed : Face)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "BVertices" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ frontier S}
local notation "retainedNonempty" => Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)

open Classical in
theorem exists_component_frontier_active (convex : Convex ℝ slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (selected : K.normalSlope seed ∈ slopes) (v : BVertices) :
    ∃ s ∈ frontier slopes, (K.componentClippedExtension retainedNonempty compact nonempty).Active
      (K.projectedVertex v.val) s := by
  obtain ⟨s, boundary, normal⟩ :=
    K.selectionComponent_boundary_normal seed convex compact no_boundary selected v.property
  have member := (K.compact_restrictedCarrier U).isClosed.frontier_subset v.property
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp member
  obtain ⟨i, corner⟩ := K.projected_corner_of_vertex_mem v.val f.val face
  have point_eq : K.componentDualPoint (f, i) = K.projectedVertex v.val := corner
  have in_roof := K.selectedCarrier_subset_footprint slopes (K.selectionComponent_carrier_subset selected member)
  have slope := compact.isClosed.frontier_subset boundary
  have height := K.clippedExtension_eq_original_of_normal compact nonempty in_roof normal slope
  have active := (K.clippedExtension_active_iff_original compact nonempty in_roof height).mpr
    ⟨slope, normal⟩
  refine ⟨s, boundary, ?_⟩
  rw [← point_eq] at active ⊢
  apply K.componentClippedExtension_active_of_retained_corner retainedNonempty compact nonempty
    (f, i) active
  rw [point_eq, height, ← point_eq]
  change -K.roofHeight (K.dualPoint (f.val, i)) = K.dualLevel (f.val, i)
  rw [K.dualPoint_roofHeight, neg_neg]

variable {I : Type*} [Finite I] [Nonempty I] (B : PolygonSideDirections I slopes)
  (compact : IsCompact slopes) (nonempty : slopes.Nonempty)

local notation "G" => K.componentClippedExtension retainedNonempty compact nonempty

/-- The exits are indexed by a fixed polygon side for each active slope.
The open rays avoid the entire original component. -/
theorem exists_component_polygon_exits
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (selected : K.normalSlope seed ∈ slopes) :
    ∃ P : (G).ExteriorPlan BVertices, P.point = (fun v => K.projectedVertex v.val) ∧
      (∀ v, P.direction (P.slope v) = B.normal (B.sideIndex (P.slope v))) ∧
      (∀ v t, 0 < t → P.ray v t ∉ S) := by
  choose slope boundary active using (fun v => K.exists_component_frontier_active seed B.convex
    compact nonempty no_boundary selected v)
  let P := B.exteriorPlan (E := G) rfl (fun v : BVertices => K.projectedVertex v.val)
    (fun _ _ h => Subtype.ext (K.projectedVertex_injective h)) slope active boundary
  refine ⟨P, rfl, fun _ => rfl, ?_⟩
  intro v t time
  exact K.componentClippedExtension_ray_avoids retainedNonempty compact nonempty (P.active v)
    rfl (P.support v) (fun h => by have := P.unit v; rw [h, norm_zero] at this; norm_num at this)
    time (fun f hf => by
      have member := K.selectionComponent_selected selected hf
      by_contra outside
      exact no_boundary f ⟨subset_closure member, outside⟩)

end Unfoldings.ConvexRoof
