module

public import Unfoldings.Roof.ConstructedFiniteTerminalBankMetric
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers

/-! Actual finite terminal-bank endpoints are original mesh vertex copies. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance terminalEndpointIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance terminalEndpointWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- The actual original source copy of the finite terminal bank. -/
def compatibleMeshTerminalStart : (T).pairedComplex.Realization (Fcut).retain :=
  K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute W r side ⟨0, le_rfl, (R.terminalTime_pos level higher r).le⟩

/-- The actual original truncation-end copy of the finite terminal bank. -/
def compatibleMeshTerminalFinish : (T).pairedComplex.Realization (Fcut).retain :=
  K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute W r side ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩

/-- Whole geometric segment coverage makes both actual endpoint copies original mesh vertices. -/
theorem exists_compatibleMeshTerminal_vertices :
    ∃ v w : (T).pairedComplex.Vertex (Fcut).retain,
      (T).pairedComplex.vertexPoint (Fcut).retain v =
        K.compatibleMeshTerminalStart compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side ∧
      (T).pairedComplex.vertexPoint (Fcut).retain w =
        K.compatibleMeshTerminalFinish compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side := by
  let i := (Fintype.equivFin (C.Vertex Set.univ)) r.val
  have first : R.cutFirst level i = K.projectedVertex r.val := by
    simp only [CompatiblePotentialRouting.cutFirst, i, Equiv.symm_apply_apply,
      CompatiblePotentialRouting.truncatedPoint]
  have last : R.cutLast level higher i = R.terminalPoint level r := by
    change R.truncatedPoint level ((R.truncatedParents level higher).parent
      (.inl ((Fintype.equivFin (C.Vertex Set.univ)).symm i))) = _
    rw [show (Fintype.equivFin (C.Vertex Set.univ)).symm i = r.val from
      (Fintype.equivFin (C.Vertex Set.univ)).symm_apply_apply r.val]
    have parent : (R.truncatedParents level higher).parent (.inl r.val) = .inr r :=
      R.parents.withLeaves_parent_root level _ r
    rw [parent]
    rfl
  have different := K.cut_endpoints_ne compact nonempty R no_boundary level higher i
  rw [first, last] at different
  have cover := K.compatibleCutMesh_segment_cover compact nonempty R no_boundary level higher
    M positive inner_disk i
  rw [first, last] at cover
  have start_position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
      (K.compatibleMeshTerminalStart compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)) = K.projectedVertex r.val := by
    have projected := (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side
      ⟨0, le_rfl, (R.terminalTime_pos level higher r).le⟩)).trans
      (SpatialEnvelope.horizontal_point M.plane _)
    exact projected.trans (by
      simp only [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points]
      rfl)
  have finish_position : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
      (K.compatibleMeshTerminalFinish compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)) = R.terminalPoint level r :=
    (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side
      ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩)).trans
      (SpatialEnvelope.horizontal_point M.plane _)
  obtain ⟨v, hv⟩ := (T).toTriangulation.exists_vertexPoint_of_segment_endpoint conforming inside
    different cover (Fcut).retain _ start_position
  have reverse_cover : segment ℝ (R.terminalPoint level r) (K.projectedVertex r.val) =
      ⋃ e : {e : (T).Index × Fin 3 // ((T).projectedTriangle e.1).edge e.2 ⊆
          segment ℝ (R.terminalPoint level r) (K.projectedVertex r.val)},
        ((T).projectedTriangle e.val.1).edge e.val.2 := by
    rw [segment_symm ℝ (R.terminalPoint level r) (K.projectedVertex r.val)]
    exact cover
  obtain ⟨w, hw⟩ := (T).toTriangulation.exists_vertexPoint_of_segment_endpoint conforming inside
    different.symm reverse_cover (Fcut).retain _ finish_position
  exact ⟨v, w, hv, hw⟩

/-- Select the original source vertex only after its exact metric-copy identity is proved. -/
def compatibleMeshTerminalStartVertex : (T).pairedComplex.Vertex (Fcut).retain :=
  (K.exists_compatibleMeshTerminal_vertices compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side).choose

/-- Select the original finite truncation vertex from the same pair of endpoint witnesses. -/
def compatibleMeshTerminalFinishVertex : (T).pairedComplex.Vertex (Fcut).retain :=
  (K.exists_compatibleMeshTerminal_vertices compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side).choose_spec.choose

@[simp] theorem vertexPoint_compatibleMeshTerminalStartVertex :
    (T).pairedComplex.vertexPoint (Fcut).retain
      (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) =
      K.compatibleMeshTerminalStart compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side :=
  (K.exists_compatibleMeshTerminal_vertices compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side).choose_spec.choose_spec.1

@[simp] theorem vertexPoint_compatibleMeshTerminalFinishVertex :
    (T).pairedComplex.vertexPoint (Fcut).retain
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) =
      K.compatibleMeshTerminalFinish compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side :=
  (K.exists_compatibleMeshTerminal_vertices compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side).choose_spec.choose_spec.2

@[simp] theorem compatibleMeshWholeMap_terminalStart :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W (K.compatibleMeshTerminalStart compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side) = bank 0 :=
  K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side _

@[simp] theorem compatibleMeshWholeMap_terminalFinish :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W (K.compatibleMeshTerminalFinish compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side) =
          bank ⟨τ, (R.terminalTime_pos level higher r).le⟩ :=
  K.compatibleMeshWholeMap_terminalBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side _

/-- The selected source vertex is exactly the original parameter-zero whole-bank copy. -/
theorem compatibleMeshWholeMap_terminalStartVertex :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W ((T).pairedComplex.vertexPoint (Fcut).retain
        (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side)) = bank 0 :=
  (congrArg (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W)
    (K.vertexPoint_compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)).trans
    (K.compatibleMeshWholeMap_terminalStart compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)

/-- The selected finish vertex is exactly the original finite whole-bank endpoint copy. -/
theorem compatibleMeshWholeMap_terminalFinishVertex :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W ((T).pairedComplex.vertexPoint (Fcut).retain
        (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side)) = bank ⟨τ, (R.terminalTime_pos level higher r).le⟩ :=
  (congrArg (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W)
    (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)).trans
    (K.compatibleMeshWholeMap_terminalFinish compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)

/-- The two finite terminal banks have distinct original truncation vertices. -/
theorem compatibleMeshTerminalFinishVertex_ne (other : Bool) (different : side ≠ other) :
    K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side ≠
        K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r other := by
  intro equal
  apply K.compatibleMeshTerminalBank_ne compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side other different
    ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩
    ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩ (R.terminalTime_pos level higher r)
  exact (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side).symm.trans
    ((congrArg ((T).pairedComplex.vertexPoint (Fcut).retain) equal).trans
      (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher
        M positive inner_disk beta acute W r other))

/-- The original source mesh vertex has precisely the prescribed original root position. -/
theorem compatibleMeshTerminalStartVertex_projection :
    (Q).projectedVertex ((T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)) = K.projectedVertex r.val := by
  have original := (T).toTriangulation.roof_projectedVertex_vertexForgetCuts conforming inside
    (Fcut).retain (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)
  have point := congrArg (fun x => Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x))
    (K.vertexPoint_compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)
  have projected := (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side
    ⟨0, le_rfl, (R.terminalTime_pos level higher r).le⟩)).trans
    (SpatialEnvelope.horizontal_point M.plane _)
  exact original.trans (point.trans (projected.trans (by
    simp only [SlopeEnvelope.ExteriorPlan.ray, zero_smul, add_zero, R.exterior_points]
    rfl)))

/-- The original finish mesh vertex is the prescribed original terminal level point. -/
theorem compatibleMeshTerminalFinishVertex_projection :
    (Q).projectedVertex ((T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side)) = R.terminalPoint level r := by
  have original := (T).toTriangulation.roof_projectedVertex_vertexForgetCuts conforming inside
    (Fcut).retain (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side)
  have point := congrArg (fun x => Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x))
    (K.vertexPoint_compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side)
  have projected := (congrArg Cap.horizontal (K.fold_compatibleMeshTerminalBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side
    ⟨τ, (R.terminalTime_pos level higher r).le, le_rfl⟩)).trans
    (SpatialEnvelope.horizontal_point M.plane _)
  exact original.trans (point.trans projected)

/-- The finite terminal bank starts at an actual nonroot of the constructed fine forest. -/
theorem compatibleMeshTerminalStartVertex_nonroot :
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) ∉ (Fcut).parents.roots := by
  let v := (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
    (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
  have projected : (Q).projectedVertex v = K.projectedVertex r.val :=
    K.compatibleMeshTerminalStartVertex_projection compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side
  have internal : (Q).projectedVertex v ∈ interior (Q).footprint := by
    rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel,
      neg_neg, projected]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel (higher r.val)
  have in_cut : (Q).projectedVertex v ∈ R.truncatedCarrier level higher :=
    Eq.mpr (congrArg (fun p : Plane => p ∈ R.truncatedCarrier level higher) projected)
      (R.vertex_mem_truncatedCarrier level higher r.val)
  intro root
  rcases (Set.ext_iff.mp (Fcut).roots_eq v).mp root with on_rim | outside_cut
  · exact ((Q).projectedVertex_mem_interior_iff v).mp internal on_rim
  · exact outside_cut in_cut

/-- The finite terminal bank ends at an actual original rim root of the fine forest. -/
theorem compatibleMeshTerminalFinishVertex_root :
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) ∈ (Fcut).parents.roots := by
  let v := (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
    (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
  have projected : (Q).projectedVertex v = R.terminalPoint level r :=
    K.compatibleMeshTerminalFinishVertex_projection compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side
  have on_rim : (Q).projectedVertex v ∈ frontier (Q).footprint := by
    rw [(T).toTriangulation.roof_footprint conforming inside, M.clip_eq_sublevel,
      neg_neg, projected]
    exact R.terminalPoint_mem_frontier level higher r
  exact (Set.ext_iff.mp (Fcut).roots_eq v).mpr
    (Or.inl (((Q).projectedVertex_mem_frontier_iff v).mp on_rim))

/-- Opposite finite source copies restore to the same original full-mesh vertex. -/
theorem compatibleMeshTerminalStartVertex_forget_eq (other : Bool) :
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) =
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r other) :=
  (Q).projectedVertex_injective
    ((K.compatibleMeshTerminalStartVertex_projection compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side).trans
      (K.compatibleMeshTerminalStartVertex_projection compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r other).symm)

/-- The distinct finite finish copies restore to the same original rim vertex. -/
theorem compatibleMeshTerminalFinishVertex_forget_eq (other : Bool) :
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r side) =
    (T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)
      (K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
        inner_disk beta acute W r other) :=
  (Q).projectedVertex_injective
    ((K.compatibleMeshTerminalFinishVertex_projection compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side).trans
      (K.compatibleMeshTerminalFinishVertex_projection compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r other).symm)

/-- The original finite bank joins distinct source and truncation vertices. -/
theorem compatibleMeshTerminalStartVertex_ne_finishVertex :
    K.compatibleMeshTerminalStartVertex compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side ≠
        K.compatibleMeshTerminalFinishVertex compact nonempty R no_boundary level higher M positive
          inner_disk beta acute W r side := by
  intro equal
  apply K.compatibleMeshTerminalStartVertex_nonroot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side
  have restored := congrArg
    ((T).pairedComplex.vertexForgetCuts (Set.subset_univ (Fcut).retain)) equal
  exact Eq.mpr (congrArg (fun v : (T).pairedComplex.Vertex Set.univ => v ∈ (Fcut).parents.roots)
    restored) (K.compatibleMeshTerminalFinishVertex_root compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side)

end Unfoldings.ConvexRoof
