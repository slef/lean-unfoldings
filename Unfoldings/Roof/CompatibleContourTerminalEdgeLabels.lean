module

public import Unfoldings.Roof.CompatibleContourRoofMarkSeparation
public import Unfoldings.Roof.CompatibleClosedPieces

/-! The original terminal ray uniquely labels its last finite edge. -/

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

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourTerminalEdgeLabelMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)

local instance contourTerminalEdgeLabelWholeFintype : Fintype W.Index := W.finiteIndex

local notation "ParentAt[" vertex "," nonroot "," side "," time "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W vertex nonroot side time

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e
local notation "BankSideAt[" e "," side "]" => TriangleComplex.contourParentBank D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts (Subtype.val e)
  (And.left (Subtype.property e)) side
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection

/-- The projection of the final finite edge is on the same ray as the true continuation. -/
theorem compatibleContourTerminalParentMark_horizontal (edge : Edge) (side : Bool)
    (t : unitInterval) :
    Cap.horizontal (W.partition.restoreCut R.carrier
      ParentAt[edge.val,edge.property.1,side,t]).val =
        R.exterior.ray (R.terminalIndex RootAt[edge])
          (R.terminalTime level RootAt[edge] - (1 - t.val) * (SpeedAt[edge]).val) := by
  let bank := BankSideAt[edge,side]
  let g := (T).pairedFolding.germDirection bank.val
  let p := (T).pairedFolding.boundaryPosition bank
  have physical (s : unitInterval) : (W.partition.restoreCut R.carrier
      ParentAt[edge.val,edge.property.1,side,s]).val = p + s.val • g :=
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W ((D).directedBoundaryPath bank s)).trans
        ((T).pairedFolding.directedBoundaryPath_position bank s)
  have endpoint : Cap.horizontal (p + g) = R.terminalPoint level RootAt[edge] := by
    have last : Cap.horizontal (p + (1 : ℝ) • g) = R.terminalPoint level RootAt[edge] :=
      (congrArg Cap.horizontal (physical 1)).symm.trans
        (K.compatibleContourTerminalEndpoint_horizontal compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W edge side)
    simpa only [one_smul] using last
  have direction := K.compatibleContourTerminalSpeed_direction compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge side
  change g = _ at direction
  have delta : p + t.val • g = (p + g) - (1 - t.val) • g := by module
  rw [physical, delta, map_sub, map_smul, endpoint, direction, map_smul, smul_smul]
  simp only [SlopeEnvelope.ExteriorPlan.spatialDirection, Cap.horizontal_horizontalAtHeight,
    CompatiblePotentialRouting.terminalPoint, SlopeEnvelope.ExteriorPlan.ray]
  module

/-- In the conforming mesh, a vertex on a selected edge is one of its actual endpoints. -/
private theorem compatibleContour_vertex_on_parent_segment
    (edge : Edge) (v : (D).Vertex Set.univ)
    (member : (Roof).projectedVertex v ∈ segment ℝ ((Roof).projectedVertex edge.val)
      ((Roof).projectedVertex ((Fcut).parents.parent edge.val))) :
    v = edge.val ∨ v = (Fcut).parents.parent edge.val := by
  let e : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots} := ⟨edge.val, edge.property.1⟩
  let seam := (Selection).edge e
  have link := (Selection).link e
  have segment_eq : segment ℝ ((Roof).projectedVertex edge.val)
      ((Roof).projectedVertex ((Fcut).parents.parent edge.val)) =
        ((Roof).projectedTriangle ((D).left seam).face).edge ((D).left seam).edge := by
    change segment ℝ ((Roof).projectedVertex e.val)
      ((Roof).projectedVertex ((Fcut).parents.parent e.val)) = _
    rcases link with ⟨first, last⟩ | ⟨first, last⟩
    · rw [last, first]
      rfl
    · rw [last, first]
      exact segment_symm ℝ _ _
  obtain ⟨flag, hv⟩ := (Roof).vertex_eq_seamEndpoint_of_projected_edge v seam
    (segment_eq.subset member)
  rcases link with ⟨first, last⟩ | ⟨first, last⟩
  · cases flag
    · exact Or.inl (hv.trans first.symm)
    · exact Or.inr (hv.trans last.symm)
  · cases flag
    · exact Or.inr (hv.trans last.symm)
    · exact Or.inl (hv.trans first.symm)

private theorem compatibleContourTerminalEdge_eq_of_speed_le
    (edge other : Edge) (same : RootAt[edge] = RootAt[other])
    (le : (SpeedAt[edge]).val ≤ (SpeedAt[other]).val) : edge = other := by
  have pos := K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W other
  let u : unitInterval := ⟨1 - (SpeedAt[edge]).val / (SpeedAt[other]).val,
    sub_nonneg.mpr ((div_le_one pos).mpr le),
    sub_le_self _ (div_nonneg (SpeedAt[edge]).property pos.le)⟩
  have time : (1 - u.val) * (SpeedAt[other]).val = (SpeedAt[edge]).val := by
    dsimp only [u]
    rw [sub_sub_cancel, div_mul_cancel₀ _ pos.ne']
  let mark := fun (b : Edge) (t : unitInterval) =>
    Cap.horizontal (W.partition.restoreCut R.carrier ParentAt[b.val,b.property.1,false,t]).val
  have eq : mark edge 0 = mark other u := by
    dsimp only [mark]
    rw [K.compatibleContourTerminalParentMark_horizontal compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge false 0,
      K.compatibleContourTerminalParentMark_horizontal compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W other false u, time]
    change R.exterior.ray (R.terminalIndex RootAt[edge])
      (R.terminalTime level RootAt[edge] - (1 - 0) * (SpeedAt[edge]).val) = _
    rw [sub_zero, one_mul, same]
  have projected (b : Edge) (t : unitInterval) : mark b t =
      AffineMap.lineMap ((Roof).projectedVertex b.val)
        ((Roof).projectedVertex ((Fcut).parents.parent b.val)) t.val := by
    let bank := BankSideAt[b,false]
    have restore := congrArg Cap.horizontal (K.restore_compatibleMeshWholeMap compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W ((D).directedBoundaryPath bank t))
    have position := congrArg Cap.horizontal ((T).pairedFolding.contourParentBank_position
      Selection contour (Fcut).boundary_roots starts b.val b.property.1 false t)
    exact restore.trans (position.trans (Cap.horizontal.toAffineMap.apply_lineMap _ _ _))
  have member : (Roof).projectedVertex edge.val ∈ segment ℝ ((Roof).projectedVertex other.val)
      ((Roof).projectedVertex ((Fcut).parents.parent other.val)) := by
    rw [segment_eq_image_lineMap]
    exact ⟨u.val, u.property, (projected other u).symm.trans (eq.symm.trans
      ((projected edge 0).trans (AffineMap.lineMap_apply_zero _ _)))⟩
  rcases K.compatibleContour_vertex_on_parent_segment compact nonempty R no_boundary level
    higher M positive inner_disk beta acute other edge.val member with at_child | at_parent
  · exact Subtype.ext at_child
  · exact (edge.property.1 (at_parent ▸ other.property.2)).elim

include contour starts W in
/-- A true terminal ray has only one last original fine edge at the fixed rim. -/
theorem compatibleContourTerminalRoot_injective :
    Function.Injective (fun edge : Edge => RootAt[edge]) := by
  intro edge other same
  rcases le_total (SpeedAt[edge]).val (SpeedAt[other]).val with le | ge
  · exact K.compatibleContourTerminalEdge_eq_of_speed_le compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge other same le
  · exact (K.compatibleContourTerminalEdge_eq_of_speed_le compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W other edge same.symm ge).symm

end Unfoldings.ConvexRoof
