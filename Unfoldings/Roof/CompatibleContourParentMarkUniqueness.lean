module

public import Unfoldings.Roof.CompatibleContourFiniteGraft
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Roof.SpatialEnvelopeFoldingGraph
public import Unfoldings.Complex.ContourParentBankUniqueness

/-! Actual finite roof-bank marks retain their labels and lie below the completion rim. -/

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

local instance contourParentMarkMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

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

local instance contourParentMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "PathAt[" v "," h "," side "," t "]" => TriangleComplex.directedBoundaryPath D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h side) t
local notation "ParentAt[" v "," h "," side "," t "]" => K.compatibleContourParentMark compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W v h side t

omit beta acute in
/-- The original convex potential is the negative of the physical roof height. -/
theorem compatibleMesh_height_eq_neg_coordinate (retain : Set (D).Seam)
    (x : (D).Realization retain) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace retain x)) =
        -((T).pairedFolding.toSpace retain x 2) := by
  have graph := congrArg (fun p : Space => p 2)
    ((T).toTriangulation.toSpace_eq_point retain x)
  rw [SpatialEnvelope.height_point, M.height_eq] at graph
  linarith

/-- Every strict finite parent-bank time lies below the original completion rim.
This includes the final fine edge whose far endpoint is on that rim. -/
theorem compatibleContourParentPath_height_lt
    (vertex : (D).Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (side : Bool) (t : unitInterval) (before : t < 1) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain
        PathAt[vertex,nonroot,side,t])) < level := by
  let child := (D).vertexPoint Set.univ vertex
  let parent := (D).vertexPoint Set.univ ((Fcut).parents.parent vertex)
  have first := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M
    positive inner_disk beta acute vertex nonroot
  change (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal ((T).pairedFolding.toSpace Set.univ child)) < level at first
  have last := (T).toTriangulation.fold_horizontal_mem_clip Set.univ parent
  rw [M.clip_eq_sublevel, neg_neg] at last
  change (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal ((T).pairedFolding.toSpace Set.univ parent)) ≤ level at last
  rw [K.compatibleMesh_height_eq_neg_coordinate compact nonempty R no_boundary level higher M
    positive inner_disk] at first last ⊢
  have position := congrArg (fun p : Space => p 2)
    ((T).pairedFolding.contourParentBank_position Selection contour (Fcut).boundary_roots starts
      vertex nonroot side t)
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.sub_apply] at position
  have strict := mul_pos (sub_pos.mpr (show (t : ℝ) < 1 from before))
    (sub_pos.mpr first)
  have bound := mul_nonneg t.property.1 (sub_nonneg.mpr last)
  have interpolated : -(t.val *
      (((T).pairedFolding.toSpace Set.univ parent) 2 -
        ((T).pairedFolding.toSpace Set.univ child) 2) +
          ((T).pairedFolding.toSpace Set.univ child) 2) < level := by nlinarith
  exact (congrArg Neg.neg position).trans_lt interpolated

/-- Equality with a strict actual finite roof-bank mark fixes its child, side, and parameter.
The other mark may be any closed finite-bank parameter. -/
theorem compatibleContourParentMark_eq_interior
    (vertex other : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots})
    (side other_side : Bool) (t s : unitInterval) (bounds : 0 < t ∧ t < 1)
    (equal : ParentAt[other.val,other.property,other_side,s] =
      ParentAt[vertex.val,vertex.property,side,t]) :
    (other, other_side, s) = (vertex, side, t) := by
  have below := K.compatibleContourParentPath_height_lt compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts vertex.val vertex.property side t
      bounds.2
  have paths := K.compatibleMeshWholeMap_injective_at compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W PathAt[vertex.val,vertex.property,side,t] below
      PathAt[other.val,other.property,other_side,s] equal.symm
  exact (D).contourParentBank_parameters_eq_of_path_eq Selection contour (Fcut).boundary_roots
    starts vertex other side other_side t s bounds paths.symm

end Unfoldings.ConvexRoof
