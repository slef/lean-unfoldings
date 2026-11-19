module

public import Unfoldings.Complex.ContourProcessedBlocks
public import Unfoldings.Roof.CompatibleContourBankAgreement

/-! The moving saved bank has one exact fan angle throughout an original child block. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance sourceOnlyChildFanIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "Event[" q "]" => TriangleComplex.PositiveContourSource D Selection q
local notation "FrontierAt[" q "," i "]" => TriangleComplex.contourFrontier D Selection q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain D Selection
  FrontierAt[q,i]


variable
  (contour : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
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

local notation "Chain[" e "]" => K.compatibleMeshFreshSourceBankChain compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts (Subtype.val e)
  (And.left (Subtype.property e)) LengthAt[contour,e] SpanAt[contour,e]
local notation "Parent" => PotentialCutForest.parents Fcut

/-- The actual retained fan at an indexed rootward bank point in the source's own stage. -/
def compatibleContourSourceBankFanAngle (e : Event[contour])
    (i : Fin (LengthAt[contour,e] + 1)) : ℝ :=
  let retain := RetainAt[contour,e.val.succ]
  (D).totalAngle retain ((D).boundaryEndVertex retain ((Chain[e]).point i))

/-- Two gap paths through the same incoming child use the same saved fan at its parent.
The index hypotheses identify both rootward banks by their original parent vertex. -/
theorem compatibleContourSourceBankFanAngle_eq_of_child
    (child : (D).Vertex Set.univ) (nonroot : child ∉ (Parent).roots)
    (a b : Event[contour]) (ia : Fin (LengthAt[contour,a] + 1))
    (ib : Fin (LengthAt[contour,b] + 1))
    (inside_a : (Parent).Ancestor VertexAt[contour,a] child)
    (inside_b : (Parent).Ancestor VertexAt[contour,b] child)
    (at_a : (Parent).parent^[ia.val] VertexAt[contour,a] = (Parent).parent child)
    (at_b : (Parent).parent^[ib.val] VertexAt[contour,b] = (Parent).parent child) :
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts a ia =
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts b ib := by
  let v := (Parent).parent child
  have nonroot_at (e : Event[contour]) (i : Fin (LengthAt[contour,e] + 1)) :
      ((Parent).parent^[i.val] VertexAt[contour,e]) ∉ (Parent).roots :=
    (Parent).iterate_lt_distanceToRoot_not_mem VertexAt[contour,e]
      ((SpanAt[contour,e]).symm ▸ i.isLt)
  have v_nonroot : v ∉ (Parent).roots := by
    intro h
    exact (nonroot_at a ia) (Eq.mpr (congrArg (· ∈ (Parent).roots) at_a) h)
  let original (u : (D).Vertex Set.univ) (h : u ∉ (Parent).roots) :=
    (D).contourParentBank Selection contour (Fcut).boundary_roots starts u h false
  have same_end (u : (D).Vertex Set.univ) (h : u ∉ (Parent).roots) (hu : u = v) :
      (original u h).val = (original v v_nonroot).val := by
    subst u
    rfl
  have raw (e : Event[contour]) (i : Fin (LengthAt[contour,e] + 1))
      (hi : (Parent).parent^[i.val] VertexAt[contour,e] = v) :
      ((Chain[e]).point i).val = (original v v_nonroot).val :=
    (K.compatibleContourSourceBank_germ compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts e i).trans
      (same_end _ (nonroot_at e i) hi)
  have original_a :
      (D).vertexOfCorner Set.univ (((Chain[a]).point ia).val.1) = v :=
    (K.compatibleMeshFreshSourceBankChain_original compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts a.val a.property.1 LengthAt[contour,a]
      SpanAt[contour,a] ia).trans at_a
  exact (D).contour_child_block_totalAngle_eq Selection contour (Fcut).boundary_roots starts
    child nonroot a.val b.val inside_a inside_b ((Chain[a]).point ia) ((Chain[b]).point ib)
    ((raw a ia at_a).trans (raw b ib at_b).symm) original_a

end Unfoldings.ConvexRoof
