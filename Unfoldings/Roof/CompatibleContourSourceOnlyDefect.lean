module

public import Unfoldings.Roof.CompatibleContourSourceOnlyChildFans
public import Unfoldings.Roof.CompatibleMeshCompleteSourceContour
public import Unfoldings.Roof.CurvatureNonnegative

/-! A complete contour makes the last original gap entry detect the parent's defect. -/

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

local instance sourceOnlyDefectAnglesIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e

variable
  (contour : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
    inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
      inner_disk beta acute).retain))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
    inner_disk).pairedComplex.contourOriginalVertex
    (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
      inner_disk beta acute).selection contour 0 ∈
    (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
      inner_disk beta acute).parents.roots)

local notation "Pcut" => PotentialCutForest.parents Fcut
local notation "Stack[" v "]" => TriangleComplex.contourSavedGapStack D Selection contour v
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e

include starts in
/-- A nonroot can have a positive defect only when its own event is the oldest
entry of its outgoing stack. This covers the empty stack as well. -/
theorem compatibleContourSourceOnly_defect_eq_zero_of_no_last_source
    (ends : (D).contourOriginalVertex Selection contour (Fin.last contour.length) ∈ (Pcut).roots)
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Pcut).roots)
    (absent : ∀ e, (Stack[v]).getLast? = some e → SourceOf[e] ≠ v) :
    (D).interiorAngularDefect Set.univ v = 0 := by
  let cap := (T).toTriangulation.normalizedCap
    (K.compatibleCutMesh_conforming compact nonempty R no_boundary level higher M positive
      inner_disk) (K.compatible_section_interior compact nonempty R level higher M)
  apply le_antisymm _ (cap.interiorCurvature_nonneg v)
  by_contra! positive
  obtain ⟨e, eq⟩ := (D).exists_positiveContourSource_of_defect Selection contour
    (Fcut).boundary_roots starts ends v nonroot positive
  obtain ⟨before, exact_stack⟩ := (D).contourSavedGapStack_source_last Selection contour
    (Fcut).boundary_roots starts e
  have name : Stack[v] = before ++ [e] := eq ▸ exact_stack
  have last : (Stack[v]).getLast? = some e := by
    rw [name, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil e []), List.getLast?_singleton]
  exact absent e last eq

end Unfoldings.ConvexRoof
