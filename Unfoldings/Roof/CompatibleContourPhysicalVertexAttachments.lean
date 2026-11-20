module

public import Unfoldings.Roof.CompatibleContourPhysicalAttachments
public import Unfoldings.Roof.CompatibleContourTerminalJoinMarks
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Roof.OriginalCutLabels

/-! The original physical endpoint addresses at finite vertices and terminal joins. -/

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

local instance sourceOnlyPhysicalVertexAttachmentsIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyPhysicalVertexAttachmentsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Height" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
local notation "Conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "Inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) Conforming Inside
local notation "Terminal" => TriangleComplex.ContourTerminalEdge D Selection
local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "TailAt[" e "," side "," t "]" => K.compatibleContourTerminalMark compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W e side t
local notation "SpeedAt[" e "]" => K.compatibleContourTerminalSpeed compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W e

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "VertexAt[" v "]" => ConvexRoof.projectedVertex Q v

local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W

/-- At a vertex below the level, all physical marks are either ends of incoming
fine edges or the start of the outgoing fine edge. -/
theorem compatibleContourPhysicalAttachmentPoint_at_vertex
    (v : (D).Vertex Set.univ) (below : Height VertexAt[v] < level)
    (a : Attachment) (s : ParamAt a) (equal : Phys a s = VertexAt[v]) :
    ∃ e : Edge, ((⟨a, s⟩ : Σ b : Attachment, ParamAt b) = ⟨.inl e, 0⟩ ∧ e.val = v) ∨
      ((⟨a, s⟩ : Σ b : Attachment, ParamAt b) = ⟨.inl e, 1⟩ ∧ (Fcut).parents.parent e.val = v) := by
  cases a with
  | inr r =>
    have tail := K.compatibleContourPhysicalAttachmentPoint_tail compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W r s
    have elapsed : R.terminalTime level RootAt[r] ≤
        R.terminalTime level RootAt[r] + (SpeedAt[r]).val * s.val :=
      le_add_of_nonneg_right (mul_nonneg (SpeedAt[r]).property s.property)
    have above := (R.terminal_ray_superlevel_iff level higher RootAt[r]
      ((R.terminalTime_pos level higher _).le.trans elapsed)).mpr elapsed
    exact (not_lt_of_ge (Eq.mp (congrArg (fun x => level ≤ Height x) (tail.symm.trans equal))
      above) below).elim
  | inl e =>
    have at_edge := K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W e s
    by_cases h₀ : s.val = 0
    · have vertex := (congrArg (AffineMap.lineMap VertexAt[e.val]
        VertexAt[(Fcut).parents.parent e.val]) h₀).trans (AffineMap.lineMap_apply_zero ..)
      have same := (Q).projectedVertex_injective (vertex.symm.trans (at_edge.symm.trans equal))
      exact ⟨e, Or.inl ⟨congrArg (fun u : unitInterval => (⟨.inl e, u⟩ : Σ b, ParamAt b))
        (Subtype.ext h₀), same⟩⟩
    by_cases h₁ : s.val = 1
    · have vertex := (congrArg (AffineMap.lineMap VertexAt[e.val]
        VertexAt[(Fcut).parents.parent e.val]) h₁).trans (AffineMap.lineMap_apply_one ..)
      have same := (Q).projectedVertex_injective (vertex.symm.trans (at_edge.symm.trans equal))
      exact ⟨e, Or.inr ⟨congrArg (fun u : unitInterval => (⟨.inl e, u⟩ : Σ b, ParamAt b))
        (Subtype.ext h₁), same⟩⟩
    have impossible : VertexAt[v] ∈ openSegment ℝ VertexAt[e.val]
        VertexAt[(Fcut).parents.parent e.val] := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨s.val, ⟨lt_of_le_of_ne s.property.1 (Ne.symm h₀), lt_of_le_of_ne s.property.2 h₁⟩,
        at_edge.symm.trans equal⟩
    exact ((Q).seamEmbedding_straight.openSegment_avoids_vertices ((Selection).link e) impossible).elim

/-- The physical point of a terminal time zero is the original truncation point. -/
theorem compatibleContourPhysicalAttachmentPoint_tail_zero (r : Terminal) :
    Phys (.inr r) 0 = R.terminalPoint level RootAt[r] := by
  calc
    _ = R.exterior.ray (R.terminalIndex RootAt[r])
      (R.terminalTime level RootAt[r] + (SpeedAt[r]).val * (0 : ℝ≥0).val) :=
        K.compatibleContourPhysicalAttachmentPoint_tail compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W r 0
    _ = _ := congrArg (R.exterior.ray (R.terminalIndex RootAt[r]))
      (by change R.terminalTime level RootAt[r] + (SpeedAt[r]).val * 0 = _; rw [mul_zero, add_zero])

set_option maxHeartbeats 2200000 in
-- The finite-edge end and the tail start have different dependent parameter types.
/-- At a terminal join, only the last fine edge and its attached true tail
give physical addresses of the join. -/
theorem compatibleContourPhysicalAttachmentPoint_at_terminal_join
    (edge : Terminal) (a : Attachment) (s : ParamAt a) (equal : Phys a s = Phys (.inr edge) 0) :
    (⟨a, s⟩ : Σ b : Attachment, ParamAt b) = ⟨.inr edge, 0⟩ ∨
      (⟨a, s⟩ : Σ b : Attachment, ParamAt b) = ⟨.inl ⟨edge.val, edge.property.1⟩, 1⟩ := by
  have tail_zero (b : Terminal) : Phys (.inr b) 0 = R.terminalPoint level RootAt[b] :=
    K.compatibleContourPhysicalAttachmentPoint_tail_zero compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W b
  have same_terminal (b : Terminal) (eq : Phys (.inr b) 0 = Phys (.inr edge) 0) : b = edge := by
    have position := (tail_zero b).symm.trans (eq.trans (tail_zero edge))
    have roots : RootAt[b] = RootAt[edge] := by
      apply Sum.inr.inj
      exact K.truncatedPoint_injective compact nonempty R no_boundary level higher
        (show R.truncatedPoint level (.inr RootAt[b]) =
          R.truncatedPoint level (.inr RootAt[edge]) from position)
    exact K.compatibleContourTerminalRoot_injective compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W roots
  cases a with
  | inr r =>
    change ℝ≥0 at s
    by_cases zero : s = 0
    · subst s
      have same := same_terminal r equal
      subst r
      exact Or.inl rfl
    · have positive_time : 0 < s := lt_of_le_of_ne zero_le (Ne.symm zero)
      have other := K.compatibleContourPhysicalAttachmentPoint_eq_of_positive_tail compact
        nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
        r s positive_time (.inr edge) 0 equal.symm
      exact Or.inl other.symm
  | inl e =>
    let destination := VertexAt[(Fcut).parents.parent e.val]
    change unitInterval at s
    have line := K.compatibleContourPhysicalAttachmentPoint_finite compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e s
    have at_level : Height (Phys (.inl e) s) = level :=
      (congrArg Height (equal.trans (tail_zero edge))).trans (R.terminalPoint_level level higher _)
    have finish : s = 1 := by
      by_contra other
      by_cases initial : s = 0
      · subst s
        have eq : Phys (.inl e) 0 = VertexAt[e.val] :=
          line.trans (AffineMap.lineMap_apply_zero ..)
        have lower := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level
          higher M positive inner_disk beta acute e.val e.property
        exact ((congrArg Height eq).trans_lt lower).ne at_level
      · have strict : 0 < s.val ∧ s.val < 1 :=
          ⟨lt_of_le_of_ne s.property.1 (fun h => initial (Subtype.ext h.symm)),
            lt_of_le_of_ne s.property.2 (fun h => other (Subtype.ext h))⟩
        exact (K.compatibleContourPhysicalAttachmentPoint_finite_lt compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W e s strict).ne at_level
    subst s
    have dest : destination = R.terminalPoint level RootAt[edge] :=
      ((AffineMap.lineMap_apply_one _ _).symm.trans line.symm).trans (equal.trans (tail_zero edge))
    have rooted : (Fcut).parents.parent e.val ∈ (Fcut).parents.roots := by
      by_contra hn
      have lt := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level
        higher M positive inner_disk beta acute ((Fcut).parents.parent e.val) hn
      exact lt.ne ((congrArg Height dest).trans (R.terminalPoint_level level higher _))
    let r : Terminal := ⟨e.val, e.property, rooted⟩
    have same_mark : Phys (.inr r) 0 = Phys (.inl e) 1 :=
      congrArg (fun x : W.Cut => Cap.horizontal (W.partition.restoreCut R.carrier x).val)
        (K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W r false)
    have same := same_terminal r (same_mark.trans equal)
    right
    exact congrArg (fun v : Terminal =>
      (⟨.inl ⟨v.val, v.property.1⟩, 1⟩ : Σ b : Attachment, ParamAt b)) same

end Unfoldings.ConvexRoof
