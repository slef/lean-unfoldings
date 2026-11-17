module

public import Unfoldings.Roof.CompatibleComparisonJunctionChart
public import Unfoldings.Roof.SpatialEnvelopeEndpointVertices
public import Unfoldings.Roof.SpatialEnvelopeVertexFibers
public import Unfoldings.Cone.PlacedTangentCenterTransport

/-! Construct the actual comparison-junction vertex and its full original halfplane fan. -/

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

local instance comparisonJunctionFanChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance comparisonJunctionFanChartWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

local notation "SourceAt[" j "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "FrontierAt[" j "]" => TriangleComplex.contourFrontier
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)
local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "ChainAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

local notation "ImageAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[j]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side j h k hk)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

open Classical in
local instance comparisonJunctionFanNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

open Classical in
/-- Enlarging the comparison window retains the actual original whole-cut junction copy. -/
theorem compatibleMeshProcessedComparisonWholeMap_rootwardJunction
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i] later ordered
      JunctionAt[i,fresh,m,length,later,ordered] = ImageAt[i,fresh,m,length] :=
  K.compatibleMeshProcessedComparisonWholeMap_lift compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W FrontierAt[i] later ordered ImageAt[i,fresh,m,length]
    ((K.compatibleMeshCurrentRootwardEnd_height compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W r side i fresh m length).trans_lt ordered)

open Classical in
/-- The fine junction keeps its original full spatial terminal coordinate. -/
theorem fold_compatibleMeshCurrentRootwardComparisonJunction
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    (NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
      NewRetainAt[FrontierAt[i],later,ordered] JunctionAt[i,fresh,m,length,later,ordered] =
      SpatialEnvelope.point M.plane (R.terminalPoint level RootAt[SourceAt[i],by omega]) := by
  have original := (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W FrontierAt[i]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side i fresh m length)).trans
      (K.fold_compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side i fresh m length)
  exact (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W FrontierAt[i] later ordered
    JunctionAt[i,fresh,m,length,later,ordered]).symm.trans
      ((congrArg (fun z => (W.partition.restoreCut CutsAt[FrontierAt[i]] z).val)
        (K.compatibleMeshProcessedComparisonWholeMap_rootwardJunction compact nonempty R no_boundary
          level higher M positive inner_disk beta acute W r side i fresh m length later
            ordered)).trans original)

open Classical in
/-- The named lifted junction is an actual retained fine vertex. Prescribed original terminal
endpoints force geometric mesh vertices, and the whole-cut fiber fixes the intrinsic bank copy. -/
theorem exists_compatibleMeshCurrentRootwardComparisonJunction_vertex
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    ∃ vertex : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Vertex
        NewRetainAt[FrontierAt[i],later,ordered],
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[FrontierAt[i],later,ordered] vertex =
          JunctionAt[i,fresh,m,length,later,ordered] := by
  let root := RootAt[SourceAt[i],by omega]
  have member : (R.terminalPoint level root, R.terminalPoint later root) ∈
      PairsAt[FrontierAt[i],later] :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩)
  let pair : {p // p ∈ PairsAt[FrontierAt[i],later]} :=
    ⟨(R.terminalPoint level root, R.terminalPoint later root), member⟩
  have different := K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level
    higher M positive inner_disk beta acute FrontierAt[i] ordered pair
  have first_member : pair.val.1 ∈ SpatialEnvelope.clip M.plane (-later) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (R.terminalPoint_level level higher root).le.trans ordered.le
  have last_member : pair.val.2 ∈ SpatialEnvelope.clip M.plane (-later) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (R.terminalPoint_level later (fun v => (higher v).trans ordered) root).le
  have cover := (NewAt[FrontierAt[i],later,ordered]).prescribed_segment_eq_union_subedges
    (fun p : {p // p ∈ PairsAt[FrontierAt[i],later]} => p.val.1) (fun p => p.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute FrontierAt[i] ordered) pair first_member last_member
  have conform := K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary
    level higher M positive inner_disk beta acute FrontierAt[i] later ordered
  have new_inside := K.compatible_section_interior compact nonempty R later
    (fun v => (higher v).trans ordered) M
  obtain ⟨full_vertex, at_vertex⟩ :=
    (NewAt[FrontierAt[i],later,ordered]).toTriangulation.vertex_of_segment_endpoint
      conform new_inside different cover
  have projected := (congrArg Cap.horizontal
    (K.fold_compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length later ordered)).trans
        (SpatialEnvelope.horizontal_point _ _)
  exact (NewAt[FrontierAt[i],later,ordered]).toTriangulation.exists_vertexPoint_of_projected_eq
    conform new_inside NewRetainAt[FrontierAt[i],later,ordered] full_vertex
    JunctionAt[i,fresh,m,length,later,ordered] (projected.trans at_vertex.symm)

open Classical in
/-- Construct the actual fine junction vertex together with its complete physically placed
original halfplane fan. Neither a vertex-copy match nor a fan certificate is an input. -/
theorem exists_compatibleMeshCurrentRootwardComparisonJunction_fan
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    ∃ vertex : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Vertex
        NewRetainAt[FrontierAt[i],later,ordered],
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[FrontierAt[i],later,ordered] vertex =
          JunctionAt[i,fresh,m,length,later,ordered] ∧
      let root := RootAt[SourceAt[i],by omega]
      ∃ tailSide : Bool, ∃ radius : ℝ, 0 < radius ∧
        ∃ a : W.partition.faceSideHalfspace ((W.terminalSupportCells root).anchor tailSide)
          (orientMap (R.exterior.point (R.terminalIndex root))
            (R.exterior.ray (R.terminalIndex root) 1)) (W.terminalSigns root),
          a.val = (M.plane (W.partition.support
            ((W.terminalSupportCells root).anchor tailSide))).project.symm
            (R.terminalPoint level root) ∧
          ∃ D : Metric.eball
              ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.tangentOrigin
                NewRetainAt[FrontierAt[i],later,ordered] vertex) (ENNReal.ofReal radius) ≃ᵢ
                Metric.ball a radius,
            ∀ (b : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.TangentTotal
                NewRetainAt[FrontierAt[i],later,ordered] vertex)
              (near : edist
                ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.tangentPoint
                  NewRetainAt[FrontierAt[i],later,ordered] vertex b)
                ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.tangentOrigin
                  NewRetainAt[FrontierAt[i],later,ordered] vertex) < ENNReal.ofReal radius),
              (M.plane (W.partition.support ((W.terminalSupportCells root).anchor tailSide))).place
                (D ⟨(NewAt[FrontierAt[i],later,ordered]).pairedComplex.tangentPoint
                  NewRetainAt[FrontierAt[i],later,ordered] vertex b, near⟩).val.val =
                  (NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
                    NewRetainAt[FrontierAt[i],later,ordered]
                    ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.tangentSurfaceTag
                      NewRetainAt[FrontierAt[i],later,ordered] vertex b) := by
  obtain ⟨vertex, position⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonJunction_vertex compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length later ordered
  obtain ⟨tailSide, ρ, ρpos, a, coordinates, H, center_H, agrees_H⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonJunction_halfplane_chart compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
      later ordered
  obtain ⟨radius, positive_radius, D, agrees⟩ :=
    (NewAt[FrontierAt[i],later,ordered]).pairedFolding.exists_placed_tangentChart_of_point_eq
      NewRetainAt[FrontierAt[i],later,ordered] vertex
      (fun z => (M.plane (W.partition.support
        ((W.terminalSupportCells RootAt[SourceAt[i],by omega]).anchor tailSide))).place z.val)
      position ρpos H center_H agrees_H
  exact ⟨vertex, position, tailSide, radius, positive_radius, a, coordinates, D, agrees⟩

end Unfoldings.ConvexRoof
