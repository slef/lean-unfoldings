module

public import Unfoldings.Roof.ComponentPotentialForest
public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Roof.SeamSegments
public import Unfoldings.Complex.FaceRestrictionVertices
public import Unfoldings.Complex.SelectedCuts
public import Unfoldings.Topology.AmbientJordanDisk

/-! The compatible original seams cut each selected component into a single disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (convex : Convex ℝ slopes) (closed : IsClosed slopes)
  (seed : Face) (selected : K.normalSlope seed ∈ slopes)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "P" => C.restrictFaces U
local notation "VertexIn" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "ι" => C.includeRestrictedVertexUniv U
local notation "F" => K.folding.restrictFaces U

open Classical in
private theorem component_vertex_projected (v : (P).Vertex Set.univ) :
    K.restrictProjection U ((P).vertexPoint Set.univ v) = K.projectedVertex (ι v) := by
  obtain ⟨⟨f, i⟩, rfl⟩ := (P).vertexOfCorner_surjective Set.univ v
  rw [C.includeRestrictedVertex_ofCorner_univ, K.projectedVertex_ofCorner]
  rfl

include convex closed selected in
open Classical in
private theorem component_vertex_projection_injective : Function.Injective ι := by
  intro v w h
  apply (P).vertexPoint_injective Set.univ
  apply K.selectionComponent_projection_injective convex closed seed selected
  rw [K.component_vertex_projected, K.component_vertex_projected, h]

include convex closed selected in
open Classical in
private theorem component_vertex_boundary_iff (v : (P).Vertex Set.univ) :
    (P).IsBoundaryVertex Set.univ v ↔ K.projectedVertex (ι v) ∈ frontier S := by
  let x := (P).vertexPoint Set.univ v
  have jordan := K.selectionComponent_frontier_isJordan convex closed seed selected
  obtain ⟨B, box⟩ := PlanarTopology.exists_ambientDiskHomeomorph
    (K.compact_restrictedCarrier U) (K.isConnected_interior_selectionComponent slopes seed).nonempty
    jordan
  let I := K.restrictProjectionHomeomorph U ⟨seed, K.seed_mem_selectionComponent slopes seed⟩ jordan
  let D := I.trans ((B.image S).trans (Homeomorph.setCongr box))
  have front : B '' frontier S = Metric.sphere (0 : Plane) 1 := by
    rw [B.image_frontier, box, frontier_closedBall (0 : Plane) one_ne_zero]
  have boundary := (F).bankBoundary_iff_disk_norm_eq_one Set.univ D x
  rw [← (P).vertexPoint_mem_bankBoundary_iff, boundary]
  change ‖B (K.restrictProjection U x)‖ = 1 ↔ _
  rw [K.component_vertex_projected]
  constructor
  · intro one
    have mem : B (K.projectedVertex (ι v)) ∈ B '' frontier S := by
      rw [front, Metric.mem_sphere, dist_zero_right]
      exact one
    obtain ⟨w, hw, equal⟩ := mem
    exact B.injective equal ▸ hw
  · intro outside
    have mem : B (K.projectedVertex (ι v)) ∈ B '' frontier S := ⟨_, outside, rfl⟩
    rwa [front, Metric.mem_sphere, dist_zero_right] at mem

include convex closed selected in
open Classical in
private def componentVertexEquiv : (P).Vertex Set.univ ≃ VertexIn :=
  Equiv.ofBijective (fun v => ⟨ι v, by
    rw [← K.component_vertex_projected]
    exact (K.range_restrictProjection U).subset (Set.mem_range_self _)⟩) <| by
      constructor
      · intro v w h
        exact K.component_vertex_projection_injective convex closed seed selected
          (congrArg Subtype.val h)
      · intro v
        obtain ⟨f, inside⟩ := Set.mem_iUnion.mp v.property
        obtain ⟨j, equal⟩ := K.projected_corner_of_vertex_mem v.val f.val inside
        refine ⟨(P).vertexOfCorner Set.univ (f, j), Subtype.ext ?_⟩
        change ι ((P).vertexOfCorner Set.univ (f, j)) = v.val
        rw [C.includeRestrictedVertex_ofCorner_univ]
        exact K.projectedVertex_injective ((K.projectedVertex_ofCorner f.val j).trans equal)

include convex closed selected

open Classical in
set_option maxHeartbeats 1900000 in
-- The transported parent selection uses dependent original edge and restricted vertex types.
/-- The actual restriction of the original selected seam cuts is a disk. -/
theorem exists_selected_component_cut_disk
    (parents : AscendingParents (C.Vertex Set.univ))
    (roots_eq : parents.roots = {v | K.projectedVertex v ∉ interior (K.selectedCarrier slopes)})
    (edges : parents.EdgeSelection C.seamGraph) :
    Nonempty ((P).Realization (C.restrictRetain U (C.selectedRetain edges)) ≃ₜ
      Metric.closedBall (0 : Plane) 1) := by
  classical
  let V := K.componentVertexEquiv convex closed seed selected
  let A := K.componentParents_of_seam_selection parents roots_eq edges seed
  let parent : AscendingParents ((P).Vertex Set.univ) := {
    roots := V ⁻¹' A.roots
    parent := fun w => V.symm (A.parent (V w))
    height := fun w => A.height (V w)
    fixed_root := fun w root => by
      rw [A.fixed_root (V w) root, V.symm_apply_apply]
    ascending := fun w nonroot => by
      rw [V.apply_symm_apply]
      exact A.ascending (V w) nonroot }
  have roots : parent.roots = (P).relativeCutRoots Set.univ := by
    ext w
    change (V w).val ∈ parents.roots ↔ (P).IsBoundaryVertex Set.univ w
    have front := K.component_vertex_boundary_iff convex closed seed selected w
    change (P).IsBoundaryVertex Set.univ w ↔ K.projectedVertex (V w).val ∈ frontier S at front
    rw [front]
    constructor
    · intro root
      refine ⟨subset_closure (V w).property, fun inside => ?_⟩
      exact ((Set.ext_iff.mp roots_eq (V w).val).mp root)
        (interior_mono (K.selectionComponent_carrier_subset selected) inside)
    · intro boundary
      apply (Set.ext_iff.mp roots_eq (V w).val).mpr
      intro inside
      exact boundary.2 (K.interior_component_of_interior_selectedCarrier inside seed (V w).property)
  have ends (e : C.Seam) {w z : C.Vertex Set.univ} (link : C.seamGraph.IsLink e w z) :
      K.projectedVertex w ∈ (K.projectedTriangle (C.left e).face).edge (C.left e).edge := by
    rw [← K.projected_link_segment link]
    exact left_mem_segment ℝ _ _
  let edge (w : {w // w ∉ parent.roots}) : (P).Seam := by
    let v := V w.val
    let t : {z // z ∉ parents.roots} := ⟨v.val, w.property⟩
    let e := edges.edge t
    have inside : K.projectedVertex v.val ∈ interior (K.selectedCarrier slopes) :=
      not_not.mp (fun h => w.property ((Set.ext_iff.mp roots_eq v.val).mpr h))
    have on_e := ends e (edges.link t)
    have on_r : K.projectedVertex v.val ∈
        (K.projectedTriangle (C.right e).face).edge (C.right e).edge :=
      (K.projected_seam_edges_eq e).subset on_e
    have both : (C.left e).face ∈ U ∧ (C.right e).face ∈ U := by
      obtain ⟨f, hf⟩ := Set.mem_iUnion.mp v.property
      exact ⟨(K.selection_label_eq_at_interior inside
        ((K.projectedTriangle _).edge_subset _ on_e) hf).trans f.property,
        (K.selection_label_eq_at_interior inside
          ((K.projectedTriangle _).edge_subset _ on_r) hf).trans f.property⟩
    exact ⟨e, both⟩
  have tagged (e : (P).Seam) (side : Bool) :
      (V ((P).seamVertex e side)).val = C.seamVertex e.val side := by
    change ι ((P).seamVertex e side) = _
    cases side <;> rfl
  let selection : parent.EdgeSelection (P).seamGraph := {
    edge := edge
    link := fun w => by
      let t : {z // z ∉ parents.roots} := ⟨(V w.val).val, w.property⟩
      have h := edges.link t
      change C.seamGraph.IsLink (edge w).val (V w.val).val (A.parent (V w.val)).val at h
      have step : V (parent.parent w.val) = A.parent (V w.val) := V.apply_symm_apply _
      have injective (p q : (P).Vertex Set.univ)
          (h : (V p).val = (V q).val) : p = q := V.injective (Subtype.ext h)
      rcases h with ⟨first, last⟩ | ⟨first, last⟩
      · exact Or.inl ⟨injective _ _ (first.trans (tagged _ _).symm),
          injective _ _ ((congrArg Subtype.val step).trans (last.trans (tagged _ _).symm))⟩
      · exact Or.inr ⟨injective _ _ (first.trans (tagged _ _).symm),
          injective _ _ ((congrArg Subtype.val step).trans (last.trans (tagged _ _).symm))⟩ }
  have retain : (P).selectedRetain selection =
      C.restrictRetain U (C.selectedRetain edges) := by
    ext s
    change s ∉ Set.range edge ↔ s.val ∉ Set.range edges.edge
    constructor
    · intro absent
      rintro ⟨v, hv⟩
      have original := ends s.val (hv ▸ edges.link v)
      have present : K.projectedVertex v.val ∈ S := Set.mem_iUnion.mpr
        ⟨(P).left s |>.face, (K.projectedTriangle _).edge_subset _ original⟩
      let w := V.symm ⟨v.val, present⟩
      have same : V w = ⟨v.val, present⟩ := V.apply_symm_apply _
      have hn : w ∉ parent.roots := by
        change ¬ (V w).val ∈ parents.roots
        rw [same]
        exact v.property
      apply absent
      refine ⟨⟨w, hn⟩, Subtype.ext ?_⟩
      have event_eq : (⟨(V w).val, hn⟩ : {z // z ∉ parents.roots}) = v := by
        apply Subtype.ext
        exact congrArg (fun p : VertexIn => p.val) same
      change edges.edge ⟨(V w).val, hn⟩ = s.val
      exact (congrArg edges.edge event_eq).trans hv
    · intro absent h
      obtain ⟨v, hv⟩ := h
      refine absent ⟨⟨(V v.val).val, v.property⟩, ?_⟩
      exact congrArg (fun t : (P).Seam => t.val) hv
  obtain ⟨disk⟩ := K.exists_selectionComponent_intrinsic_disk convex closed seed selected
  rw [← retain]
  exact ⟨(P).selectedCutDisk selection roots F disk⟩

variable {E : SlopeEnvelope} {a β : ℝ}
  (I : K.CommonPotentialRouting {f | K.normalSlope f ∈ slopes} E a β)

open Classical in
/-- The common-potential forest cuts the selected component to the disk with
its original seam names. -/
theorem exists_compatible_component_cut_disk :
    Nonempty ((P).Realization (C.restrictRetain U (C.selectedRetain I.selection)) ≃ₜ
      Metric.closedBall (0 : Plane) 1) :=
  K.exists_selected_component_cut_disk convex closed seed selected I.parents I.roots_eq I.selection

end Unfoldings.ConvexRoof
