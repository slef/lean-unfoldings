module

public import Unfoldings.Complex.ContourSavedFanAngles
public import Unfoldings.Complex.ContourParentWedgeRun
public import Unfoldings.Roof.CompatibleContourSourceOnlyChildFans

/-! The actual saved bank angles and the contour interval of final roof wedges. -/

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

local instance sourceOnlyFanIntervalIndexFintype : Fintype (T).Index :=
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

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection contour j
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval D Selection contour
  (PotentialCutForest.boundary_roots Fcut) starts v h

private theorem actual_bank_fan_saved_copy
    (e : Event[contour]) (i : Fin (LengthAt[contour,e] + 1))
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (same : (Parent).parent^[i.val] VertexAt[contour,e] = v) :
    let stage := RetainAt[contour,e.val.succ]
    let inc := (D).selectedRetain_subset_processed Selection FrontierAt[contour,e.val.succ]
    let data := Interval[v,nonroot]
    (Selection).edge ⟨v, nonroot⟩ ∉ stage ∧
      ((D).boundaryEndVertex stage ((Chain[e]).point i)) =
        (D).vertexForgetCuts inc ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point data.leave)) := by
  let stage := RetainAt[contour,e.val.succ]
  let data := Interval[v,nonroot]
  have same_named (w : (D).Vertex Set.univ) (not_root : w ∉ (Parent).roots)
      (h : w = v) :
      ((D).contourParentBank Selection contour (Fcut).boundary_roots starts w not_root false).val =
        (contour.cycle.point data.leave).val := by
    subst w
    rfl
  have raw : ((Chain[e]).point i).val = (contour.cycle.point data.leave).val :=
    (K.compatibleContourSourceBank_germ compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts e i).trans (same_named _ _ same)
  have boundary : (D).IsBoundaryEdge stage ((D).germEdge (contour.cycle.point data.leave).val) :=
    (congrArg ((D).germEdge) raw) ▸ ((Chain[e]).point i).property
  have side : (D).germEdge (contour.cycle.point data.leave).val =
      (D).seamSide ((Selection).edge ⟨v, nonroot⟩) (!data.side) :=
    congrArg Subtype.val data.exit_named
  rw [side] at boundary
  have cut : (Selection).edge ⟨v, nonroot⟩ ∉ stage := by
    cases h : !data.side
    · rw [h] at boundary
      exact ((D).isBoundaryEdge_left_iff stage _).mp boundary
    · rw [h] at boundary
      exact ((D).isBoundaryEdge_right_iff stage _).mp boundary
  exact ⟨cut, congrArg (fun g : (D).Germ => (D).vertexOfCorner stage g.1) raw⟩

open scoped Classical in
/-- The loss between two literal saved openings at the same parent is the sum of the
actual original roof wedges between the two processing times along the contour. -/
theorem compatibleContourSourceBankFanAngle_sub_eq_contour_sum
    (e f : Event[contour]) (i : Fin (LengthAt[contour,e] + 1))
    (j : Fin (LengthAt[contour,f] + 1))
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (earlier : e.val.val ≤ f.val.val)
    (old_parent : (Parent).parent^[i.val] VertexAt[contour,e] = v)
    (new_parent : (Parent).parent^[j.val] VertexAt[contour,f] = v) :
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts e i -
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts f j =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (contour.length + 1) =>
        Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val),
        (D).totalAngle (Fcut).retain ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point t)) := by
  obtain ⟨old_cut, old_fan⟩ := actual_bank_fan_saved_copy K compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts e i v nonroot old_parent
  obtain ⟨new_cut, new_fan⟩ := actual_bank_fan_saved_copy K compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts f j v nonroot new_parent
  have formula := (D).contourSavedParentFan_angle_sub_eq_sum Selection contour
    (Fcut).boundary_roots starts v nonroot e.val.succ f.val.succ (Nat.succ_le_succ earlier)
    old_cut new_cut
  simp only [compatibleContourSourceBankFanAngle]
  rw [old_fan, new_fan]
  exact formula

open scoped Classical in
/-- Summing over the ordered roof run gives the same aperture difference as
summing over the corresponding original contour positions. -/
theorem compatibleContourSourceBankFanAngle_sub_eq_wedge_run
    (e f : Event[contour]) (i : Fin (LengthAt[contour,e] + 1))
    (j : Fin (LengthAt[contour,f] + 1))
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Parent).roots)
    (earlier : e.val.val ≤ f.val.val)
    (old_parent : (Parent).parent^[i.val] VertexAt[contour,e] = v)
    (new_parent : (Parent).parent^[j.val] VertexAt[contour,f] = v)
    (first last : Fin (contour.length + 1))
    (A : (D).ContourParentWedgeRun Selection contour (Fcut).boundary_roots starts v first last)
    (names : ∀ t : Fin (contour.length + 1), (∃ k, A.visit k = t) ↔
      Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val) :
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts e i -
    K.compatibleContourSourceBankFanAngle compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts f j =
      ∑ k : Fin (A.length + 1), (D).totalAngle (Fcut).retain
        ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point (A.visit k))) := by
  classical
  let interval := Finset.univ.filter (fun t : Fin (contour.length + 1) =>
    Visit[t] = v ∧ t ≠ (Interval[v,nonroot]).leave ∧ e.val.val ≤ t.val ∧ t.val < f.val.val)
  let angle (t : Fin (contour.length + 1)) :=
    (D).totalAngle (Fcut).retain ((D).boundaryEndVertex (Fcut).retain (contour.cycle.point t))
  have cover : Finset.univ.map A.visit.toEmbedding = interval := by
    ext t
    simp only [interval, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    exact names t
  rw [K.compatibleContourSourceBankFanAngle_sub_eq_contour_sum compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts e f i j v nonroot earlier
    old_parent new_parent]
  change (∑ t ∈ interval, angle t) = ∑ k, angle (A.visit k)
  rw [← cover, Finset.sum_map]
  rfl

end Unfoldings.ConvexRoof
