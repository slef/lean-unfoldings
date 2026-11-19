module

public import Unfoldings.Roof.CompatibleContourTerminalEdgeLabels
public import Unfoldings.Geometry.OpeningStraightTail
public import Unfoldings.Geometry.OrientedBankGap

/-! Canonical gap banks continue straight through their named rim endpoint. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open PolygonalChain

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

local instance contourGapTerminalStraightMeshFintype : Fintype (T).Index :=
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

local instance contourGapTerminalStraightWholeFintype : Fintype W.Index := W.finiteIndex


local notation "P" => PotentialCutForest.parents Fcut
local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection

local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Roof" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside

/-- Choosing the terminal ray depends only on the endpoint of the actual fine history. -/
private theorem compatibleMeshTerminalRoot_eq_of_root_eq
    (start other : (T).pairedComplex.Vertex Set.univ)
    (nontrivial : 0 < (Fcut).parents.distanceToRoot start)
    (other_nontrivial : 0 < (Fcut).parents.distanceToRoot other)
    (same : (Fcut).parents.root start = (Fcut).parents.root other) :
    K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M positive inner_disk
      beta acute start nontrivial =
    K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M positive inner_disk
      beta acute other other_nontrivial := by
  have first := K.compatibleMeshTerminalRoot_point compact nonempty R no_boundary level higher M
    positive inner_disk beta acute start nontrivial
  have last := K.compatibleMeshTerminalRoot_point compact nonempty R no_boundary level higher M
    positive inner_disk beta acute other other_nontrivial
  have equal := first.symm.trans ((congrArg (Roof).projectedVertex same).trans last)
  exact Sum.inr.inj (K.truncatedPoint_injective compact nonempty R no_boundary level higher
    (show R.truncatedPoint level (.inr _) = R.truncatedPoint level (.inr _) from equal))

omit beta acute in
private theorem terminalChild_at_last {V : Type*} [Finite V] (parents : AscendingParents V) (v : V)
    (i : Fin (parents.distanceToRoot v)) (last : i.val + 1 = parents.distanceToRoot v) :
    parents.parent^[i.val] v ∉ parents.roots ∧
      parents.parent (parents.parent^[i.val] v) ∈ parents.roots := by
  refine ⟨parents.iterate_lt_distanceToRoot_not_mem v i.isLt, ?_⟩
  rw [← Function.iterate_succ_apply' parents.parent i.val v, show i.val.succ = _ from last]
  exact parents.iterate_distanceToRoot_mem v

include contour starts W in
/-- Every nonroot source of the same fine tree reaches the same final child. -/
theorem compatibleContour_ancestor_last_child
    (v source : (D).Vertex Set.univ) (i : Fin ((P).distanceToRoot v))
    (last : i.val + 1 = (P).distanceToRoot v)
    (nonroot : source ∉ (P).roots) (same : (P).root source = (P).root v) :
    (P).Ancestor source ((P).rootwardVertexPath v i.castSucc) := by
  let d := (P).distanceToRoot source
  have positive_d : 0 < d := Nat.pos_of_ne_zero
    (fun hz => nonroot (((P).distanceToRoot_eq_zero_iff source).mp hz))
  let j : Fin d := ⟨d - 1, by omega⟩
  have jlast : j.val + 1 = d := by
    change (d - 1) + 1 = d
    omega
  let e : Edge := ⟨(P).parent^[i.val] v,
    terminalChild_at_last (P) v i last⟩
  let other : Edge := ⟨(P).parent^[j.val] source,
    terminalChild_at_last (P) source j jlast⟩
  have e_root : (P).root v = (P).root e.val := (P).root_eq_of_ancestor ⟨i.val, rfl⟩
  have other_root : (P).root source = (P).root other.val :=
    (P).root_eq_of_ancestor ⟨j.val, rfl⟩
  have same_root : (P).root other.val = (P).root e.val :=
    other_root.symm.trans (same.trans e_root)
  have ray := K.compatibleMeshTerminalRoot_eq_of_root_eq compact nonempty R no_boundary level
    higher M positive inner_disk beta acute other.val e.val
    ((D).contourTerminalEdge_positive Selection other)
    ((D).contourTerminalEdge_positive Selection e) same_root
  have label := K.compatibleContourTerminalRoot_injective compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W ray
  exact ⟨j.val, congrArg Subtype.val label⟩

include starts W in
/-- No positive opening on the constructed path hinges at the artificial truncation rim. -/
theorem compatibleContourRootwardOpenings_hinge_le_last
    (v : (D).Vertex Set.univ) (i : Fin ((P).distanceToRoot v))
    (last : i.val + 1 = (P).distanceToRoot v) (stage : Fin (contour.length + 1))
    (opening : Opening ((P).distanceToRoot v))
    (member : opening ∈ (D).contourRootwardOpenings Selection contour stage v) :
    opening.hinge ≤ i.castSucc := by
  let root : {z // z ∈ (P).roots} := ⟨(P).root v, (P).root_mem v⟩
  let seeds := ((D).selectedContourSeeds Selection contour).take stage.val
  let path := (P).rootwardVertexPath v
  let sources := (P).historySources seeds root
  let weight := (D).interiorAngularDefect Set.univ
  let reaches (s) (hs : s ∈ sources) : ∃ j, (P).Ancestor s (path j) :=
    ⟨Fin.last ((P).distanceToRoot v), by
      simpa only [path, AscendingParents.rootwardVertexPath_last] using
        (P).historySources_ancestor seeds root s hs⟩
  classical
  change opening ∈ withoutZeroOpenings ((P).ancestorOpenings path weight sources reaches) at member
  have filtered := List.mem_filter.mp member
  have angle : opening.angle ≠ 0 := of_decide_eq_true filtered.2
  obtain ⟨source, _, label⟩ := List.mem_map.mp filtered.1
  have hinge : opening.hinge = (P).firstAncestorIndex path source.val
      (reaches source.val source.property) := (congrArg Opening.hinge label).symm
  rw [hinge]
  apply ((P).firstAncestorIndex_le_iff path ((P).rootwardVertexPath_ancestor v)
    source.val (reaches source.val source.property) i.castSucc).mpr
  have related := (P).historySources_ancestor seeds root source.val source.property
  have same : (P).root source.val = (P).root v :=
    (P).ancestor_root_unique ((P).ancestor_root source.val) related
      ((P).root_mem source.val) ((P).root_mem v)
  apply K.compatibleContour_ancestor_last_child compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W v source.val i last _ same
  intro isroot
  have at_root := (P).ancestor_root_unique ((P).ancestor_refl source.val) related
    isroot ((P).root_mem v)
  have at_rim : (D).IsBoundaryVertex Set.univ root.val :=
    (Fcut).root_isBoundaryVertex v (Nat.zero_lt_of_lt i.isLt)
  apply angle
  have value : opening.angle = weight source.val := (congrArg Opening.angle label).symm
  rw [value, at_root]
  simp only [weight, TriangleComplex.interiorAngularDefect, ite_eq_left at_rim]

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SpanAt[" e "]" => TriangleComplex.positiveContourBank_span D Selection contour e
local notation "LengthAt[" e "]" =>
  TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts e
local notation "OpenedAt[" e "]" => K.compatibleContourOpenedBank compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e

include W in
/-- The constructed last opened edge and its unbounded tail have the exact same vector. -/
theorem compatibleContourOpenedBank_straightTail (event : Event) :
    (OpenedAt[event]).direction = (OpenedAt[event]).chain.edge (Fin.last LengthAt[event]) := by
  let v := (D).positiveContourVertex Selection contour event
  let stage := event.val.succ
  let i : Fin ((P).distanceToRoot v) := Fin.cast SpanAt[event].symm (Fin.last LengthAt[event])
  have last : i.val + 1 = (P).distanceToRoot v := SpanAt[event].symm
  let list := (D).contourRootwardOpenings Selection contour stage v
  change ((BankAt[event]).openings (castOpenings SpanAt[event] list)).direction =
    ((BankAt[event]).openings (castOpenings SpanAt[event] list)).chain.edge
      (Fin.last LengthAt[event])
  apply (BankAt[event]).openings_straightTail _ _ rfl
  intro e member
  obtain ⟨o, present, rfl⟩ := List.mem_map.mp member
  exact K.compatibleContourRootwardOpenings_hinge_le_last compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W v i last stage o present

include W in
/-- On both canonical gap banks, the rim endpoint is a named subdivision of a straight bank. -/
theorem compatibleContourGapBank_straightTail (event : Event)
    (G : OrientedBankGap (BankAt[event]) (OpenedAt[event])) (side : Bool) :
    (G.model.bank side).direction = (G.model.bank side).chain.edge (Fin.last LengthAt[event]) := by
  cases side
  · rfl
  · exact K.compatibleContourOpenedBank_straightTail compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W event

end Unfoldings.ConvexRoof
