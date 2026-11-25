module

public import Unfoldings.FewestNets.ThreeExitSourceGaps
public import Unfoldings.FewestNets.ThreeExitRimLinks
public import Unfoldings.Roof.PotentialContourPhysical
public import Unfoldings.Roof.OriginalCutLabels

/-! The last link and the continued tail of each contour bank come from the same original exit. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}

variable (level : ℝ)
  (M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "T[" higher "]" => R.fineMesh level M higher
local notation "D[" higher "]" => SpatialEnvelope.FloorMesh.pairedComplex (T[higher])
local notation "Q[" higher "]" => SpatialEnvelope.FloorMesh.roof (T[higher])
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
local notation "F[" higher "]" => R.fineMeshForest level M higher
local notation "σ[" higher "]" => PotentialCutForest.selection (F[higher])

local instance tailMeshIndexFintype (higher : ∀ v : V, (G).height (p v) < level) :
    Fintype (T[higher]).Index := @Fintype.ofFinite _ (T[higher]).finite

/-- The selected edge into a fine forest root is a terminal subsegment
of one actual original exit. Its parent lies at the affine floor. -/
theorem exists_exit_of_fineMesh_terminalParent
    (higher : ∀ v : V, (G).height (p v) < level)
    (child : (D[higher]).Vertex Set.univ) (nonroot : child ∉ (F[higher]).parents.roots)
    (rooted : (F[higher]).parents.parent child ∈ (F[higher]).parents.roots) :
    ∃ (r : Root) (t : ℝ), 0 ≤ t ∧ t < R.exits.timeAtLevel level (R.exitRoot r) ∧
      (Q[higher]).projectedVertex child = R.exits.ray (R.exitRoot r) t ∧
      (Q[higher]).projectedVertex ((F[higher]).parents.parent child) =
        R.exits.pointAtLevel level (R.exitRoot r) := by
  let root := (F[higher]).parents.parent child
  obtain ⟨segment⟩ := R.fineMesh_parent_alignment level M higher child nonroot
  have on_cut : (Q[higher]).projectedVertex root ∈ (R.truncatedEmbedding level higher).carrier := by
    have endpoint : (R.truncatedEmbedding level higher).edge segment.edge
        ⟨segment.last, segment.last_mem⟩ = (Q[higher]).projectedVertex root := segment.at_last
    rw [← endpoint]
    exact (R.truncatedEmbedding level higher).mem_carrier_edge segment.edge _
  have on_boundary : (D[higher]).IsBoundaryVertex Set.univ root :=
    ((Set.ext_iff.mp (F[higher]).roots_eq root).mp rooted).resolve_right (fun outside => outside on_cut)
  have not_internal : (Q[higher]).projectedVertex root ∉ interior ((Q[higher]).footprint) :=
    fun inside => ((Q[higher]).projectedVertex_mem_interior_iff root).mp inside on_boundary
  have at_most : (G).height ((Q[higher]).projectedVertex root) ≤ level := by
    have member := (Q[higher]).projectedVertex_mem_footprint root
    rw [(T[higher]).roof_footprint, M.clipAbove_referenceFloor_eq] at member
    exact member
  have from_below : ¬ (G).height ((Q[higher]).projectedVertex root) < level := by
    intro h
    apply not_internal
    rw [(T[higher]).roof_footprint, M.clipAbove_referenceFloor_eq]
    exact (G).mem_interior_sublevel h
  exact R.exists_exit_of_subsegment_to_rim level higher
    (le_antisymm at_most (le_of_not_gt from_below)) segment

set_option maxHeartbeats 1500000 in
-- The finite source, fine forest root and final physical edge share their actual vertex labels.
/-- The last link of the saved contour chain has true nonnegative exit
parameters and ends at its exact affine-floor truncation. -/
theorem contourSource_last_link_on_exit
    (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex σ[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource σ[higher] contour) :
    let n := (D[higher]).positiveContourBankLength σ[higher] contour event
    let chain := (Q[higher]).folding.projectedBoundaryChain
      ((F[higher]).contourSourceBankChain contour starts event)
    ∃ (r : Root) (t : ℝ), 0 ≤ t ∧ t < R.exits.timeAtLevel level (R.exitRoot r) ∧
      chain.vertex (Fin.last n).castSucc = R.exits.ray (R.exitRoot r) t ∧
      chain.vertex (Fin.last (n + 1)) = R.exits.pointAtLevel level (R.exitRoot r) := by
  dsimp only
  let n := (D[higher]).positiveContourBankLength σ[higher] contour event
  let bank := (F[higher]).contourSourceBankChain contour starts event
  let chain := (Q[higher]).folding.projectedBoundaryChain bank
  let source := (D[higher]).positiveContourVertex σ[higher] contour event
  let child := (F[higher]).parents.parent^[n] source
  have nonroot : child ∉ (F[higher]).parents.roots :=
    (F[higher]).parents.iterate_lt_distanceToRoot_not_mem source
      (by rw [(D[higher]).positiveContourBank_span σ[higher] contour event]; omega)
  have rooted : (F[higher]).parents.parent child ∈ (F[higher]).parents.roots := by
    have at_root := (F[higher]).parents.iterate_distanceToRoot_mem source
    rw [(D[higher]).positiveContourBank_span σ[higher] contour event,
      Function.iterate_succ_apply'] at at_root
    exact at_root
  obtain ⟨r, t, nonnegative, before, first, last⟩ :=
    R.exists_exit_of_fineMesh_terminalParent level M higher child nonroot rooted
  refine ⟨r, t, nonnegative, before, ?_, ?_⟩
  · change chain.vertex (Fin.last n).castSucc = _
    rw [(F[higher]).contourSourceBankChain_projected_vertex contour starts event]
    exact first
  · change chain.vertex (Fin.last (n + 1)) = _
    rw [(F[higher]).contourSourceBankChain_projected_vertex contour starts event,
      Fin.val_last, Function.iterate_succ_apply']
    exact last


private theorem fineMesh_boundary_position
    (higher : ∀ v : V, (G).height (p v) < level) {retain : Set (D[higher]).Seam}
    (q : (D[higher]).BoundaryEnd retain) :
    (Q[higher]).folding.boundaryPosition q = SpatialEnvelope.point M.plane
      (Cap.horizontal ((Q[higher]).folding.boundaryPosition q)) := by
  rw [(Q[higher]).folding.boundaryPosition_raw]
  let i := q.val.1.1
  let x := ((T[higher]).triangle i).vertex q.val.1.2
  change (T[higher]).placement i x = SpatialEnvelope.point M.plane
    (Cap.horizontal ((T[higher]).placement i x))
  rw [show Cap.horizontal ((T[higher]).placement i x) =
      (M.plane ((T[higher]).support i)).project x from (M.plane ((T[higher]).support i)).horizontal_place x]
  exact (T[higher]).placement_eq_point i (((T[higher]).triangle i).vertex_mem _)

set_option maxHeartbeats 1400000 in
-- The physical direction retains the true vertical component throughout the extension.
/-- The whole physical tail of the original saved bank is the actual exit
ray from the rim onward, with the exact parameter scaling of its last fine link. -/
theorem contourSource_physical_tail
    (higher : ∀ v : V, (G).height (p v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex σ[higher] contour 0 ∈ (F[higher]).parents.roots)
    (event : (D[higher]).PositiveContourSource σ[higher] contour) :
    ∃ (r : Root) (first : ℝ), 0 ≤ first ∧
      let τ := R.exits.timeAtLevel level (R.exitRoot r)
      first < τ ∧ ∀ s : ℝ≥0,
        ((F[higher]).contourSourceSpatialRay contour starts event).tail s =
          SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) (τ + s.val * (τ - first))) := by
  obtain ⟨r, t, nonneg, before, start, finish⟩ :=
    R.contourSource_last_link_on_exit level M higher contour starts event
  let n := (D[higher]).positiveContourBankLength σ[higher] contour event
  let path := (F[higher]).contourSourceSpatialRay contour starts event
  let bank := (F[higher]).contourSourceBankChain contour starts event
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have τ_nonneg : 0 ≤ τ := nonneg.trans before.le
  have positive : 0 < τ - t := sub_pos.mpr before
  have start_at : path.chain.vertex (Fin.last n).castSucc =
      SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t) := by
    change ((Q[higher]).folding.boundarySpatialChain bank).vertex (Fin.last n).castSucc = _
    change ((Q[higher]).folding.projectedBoundaryChain bank).vertex (Fin.last n).castSucc = _ at start
    rw [(Q[higher]).folding.projectedBoundaryChain_vertex_castSucc] at start
    rw [(Q[higher]).folding.boundarySpatialChain_vertex_castSucc,
      R.fineMesh_boundary_position level M higher, start]
  have finish_at : path.chain.vertex (Fin.last (n + 1)) =
      SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) τ) := by
    change ((Q[higher]).folding.boundarySpatialChain bank).vertex (Fin.last (n + 1)) = _
    change ((Q[higher]).folding.projectedBoundaryChain bank).vertex (Fin.last (n + 1)) = _ at finish
    rw [(Q[higher]).folding.projectedBoundaryChain_vertex_last] at finish
    rw [(Q[higher]).folding.boundarySpatialChain_vertex_last,
      R.fineMesh_boundary_position level M higher, finish]
    rfl
  have vector : path.direction = (τ - t) • R.physicalRayDirection r := by
    change path.chain.vertex (Fin.last n).succ - path.chain.vertex (Fin.last n).castSucc = _
    rw [Fin.succ_last, finish_at, start_at, R.physical_point_ray M r τ_nonneg,
      R.physical_point_ray M r nonneg, add_sub_add_left_eq_sub, sub_smul]
  refine ⟨r, t, nonneg, before, ?_⟩
  intro s
  change path.tail s = _
  have after : 0 ≤ τ + s.val * (τ - t) := add_nonneg τ_nonneg
    (mul_nonneg s.property positive.le)
  rw [PolygonalRay.tail, finish_at, vector, R.physical_point_ray M r τ_nonneg,
    R.physical_point_ray M r after, smul_smul, add_smul, add_assoc]
  rfl

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
