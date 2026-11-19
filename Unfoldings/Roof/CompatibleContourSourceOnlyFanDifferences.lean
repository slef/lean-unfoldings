module

public import Unfoldings.Complex.NestedFanAngles
public import Unfoldings.Complex.ContourContactFans
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildFans

/-! The angle between two saved openings is accounted for by final roof wedges. -/

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

local instance sourceOnlyFanDifferenceIndexFintype : Fintype (T).Index :=
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

open scoped Classical in
/-- At one literal outgoing bank, the later saved fan has lost exactly the full-cut
roof copies that lie in the earlier fan and outside the later fan. -/
theorem compatibleContourSourceBankFanAngle_difference
    (e f : Event[contour]) (i : Fin (LengthAt[contour,e] + 1))
    (j : Fin (LengthAt[contour,f] + 1))
    (earlier : e.val.val ≤ f.val.val)
    (same : (Parent).parent^[i.val] VertexAt[contour,e] =
      (Parent).parent^[j.val] VertexAt[contour,f]) :
    let old := RetainAt[contour,e.val.succ]
    let new := RetainAt[contour,f.val.succ]
    let w := (D).boundaryEndVertex old ((Chain[e]).point i)
    let v := (D).boundaryEndVertex new ((Chain[f]).point j)
    ∃ (old_cut : (Fcut).retain ⊆ old) (new_cut : (Fcut).retain ⊆ new),
      K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts e i -
      K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts f j =
        ∑ u ∈ Finset.univ.filter (fun u : (D).Vertex (Fcut).retain =>
          (D).vertexForgetCuts old_cut u = w ∧ (D).vertexForgetCuts new_cut u ≠ v),
          (D).totalAngle (Fcut).retain u := by
  let old := RetainAt[contour,e.val.succ]
  let new := RetainAt[contour,f.val.succ]
  have more : (FrontierAt[contour,e.val.succ]).processed ⊆
      (FrontierAt[contour,f.val.succ]).processed := by
    intro v h
    have old_state := (D).rim_contour_processed_iff_of_boundary_roots Selection
      (Fcut).boundary_roots contour starts e.val.succ v
    have new_state := (D).rim_contour_processed_iff_of_boundary_roots Selection
      (Fcut).boundary_roots contour starts f.val.succ v
    apply new_state.mpr
    rcases old_state.mp h with root | ⟨k, past, label⟩
    · exact Or.inl root
    · exact Or.inr ⟨k, past.trans_le (Nat.succ_le_succ earlier), label⟩
  have nested : new ⊆ old := (D).processedParentRetain_antitone Selection more
  have small : (Fcut).retain ⊆ new := (D).selectedRetain_subset_processed Selection _
  have same_named (u v : (D).Vertex Set.univ) (hu : u ∉ (Parent).roots)
      (hv : v ∉ (Parent).roots) (h : u = v) :
      ((D).contourParentBank Selection contour (Fcut).boundary_roots starts u hu false).val =
        ((D).contourParentBank Selection contour (Fcut).boundary_roots starts v hv false).val := by
    subst v
    rfl
  have bank : ((Chain[e]).point i).val = ((Chain[f]).point j).val :=
    (K.compatibleContourSourceBank_germ compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts e i).trans
      ((same_named _ _ _ _ same).trans
        (K.compatibleContourSourceBank_germ compact nonempty R no_boundary level higher M positive
          inner_disk beta acute contour starts f j).symm)
  refine ⟨small.trans nested, small, ?_⟩
  exact (D).boundaryFanAngle_sub_of_nested_copies small nested
    ((Chain[e]).point i) ((Chain[f]).point j) bank

end Unfoldings.ConvexRoof
