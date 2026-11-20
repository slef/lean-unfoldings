module

public import Unfoldings.Cone.MarkedSlitRestoration
public import Unfoldings.Metric.BankStackIncidentSlots
public import Unfoldings.Roof.CompatibleContourSourceOnlyEmptyStackClass
public import Unfoldings.Roof.CompatibleContourSourceOnlyDefect
public import Unfoldings.Roof.CompatibleContourCalibratedRoofEndpoints
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels

/-! A flat leaf restores the two sides of the original full-turn slit. -/

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

local instance sourceOnlyEmptyStackLeafBallIndexFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyEmptyStackLeafBallWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, ParamAt (Sigma.fst s))

local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e


local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection contour (PotentialCutForest.boundary_roots Fcut) starts v h
local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle contour) j)))) :
      MetricGluing.Total Pieces)

local notation "Germ" => K.compatibleContourFiniteRoofGerm compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts
local notation "Point" => MetricGluing.point Pieces Banks

set_option maxHeartbeats 3200000 in
-- The incidence tests carry the dependent types of the actual roof marks.
/-- The only roof copy at an empty-stack leaf is a full-turn slit.
Restoring its original outgoing bank gives a planar ball. -/
theorem compatibleContourSourceOnlyEmptyStack_leaf_planarBall
    (ends : (D).contourOriginalVertex Selection contour (Fin.last contour.length) ∈
      (Fcut).parents.roots)
    (parent : Edge) (none_added : Stack FiniteBank[parent.val,parent.property] = [])
    (leaf : ((D).contourFullParentWedgeRun Selection contour
      (Fcut).boundary_roots starts parent).length = 0) :
    HasMetricBallChart ℂ (Point (EndAt true ⟨FiniteBank[parent.val,parent.property], 0⟩ 0)) := by
  let b := FiniteBank[parent.val,parent.property]
  let A := (D).contourFullParentWedgeRun Selection contour (Fcut).boundary_roots starts parent
  obtain ⟨H, first_center, roof_center, route, _, _, _⟩ :=
    K.exists_compatibleContourSourceOnlyEmptyStackClass compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models parent none_added
  let j := A.visit 0
  let w := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain w)
  let a : MetricGluing.Total Pieces := ⟨none, x⟩
  have center : H.center 0 = a := roof_center 0
  have only (i : Fin (A.length + 1)) : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have h := i.isLt
    change A.length = 0 at leaf
    omega
  have orbit (z : MetricGluing.Total Pieces) : Relation.EqvGen Banks a z → z = a := by
    intro h
    rw [← center] at h
    obtain ⟨i, hi⟩ := (H.eqvGen_iff z).mp h
    exact (hi.trans (congrArg H.center (only i))).trans center
  have only_slot (s : Time) (haz : L s.1 s.2 = a) : s = ⟨⟨b, 0⟩, 0⟩ := by
    obtain ⟨i, hi⟩ := H.incident 0 false s (haz.trans center.symm)
    rw [hi, route, show i = Fin.last A.length from (only i).trans (only _).symm,
      MetricGluing.BankStackCyclicClass.roofTime_last]
  have first_germ : Germ parent true false = (D).boundaryMate Retain (contour.cycle.point j) :=
    ((D).contourParent_firstVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans
      (congrArg (fun i => (D).boundaryMate Retain (contour.cycle.point i)) A.at_first.symm)
  have last_germ : Germ parent false false = contour.cycle.point j := by
    have h := ((D).contourParent_lastVisit_germ Selection contour (Fcut).boundary_roots starts
      parent.val parent.property).symm.trans (congrArg contour.cycle.point A.at_last.symm)
    rw [only (Fin.last A.length)] at h
    exact h
  let s := Germ parent true false
  let q := Germ parent false false
  have at_w : (D).boundaryEndVertex Retain s = w :=
    ((D).boundaryEnd_vertex_eq_iff Retain _ _).mpr (Or.inr first_germ)
  have mate : (D).boundaryMate Retain s = q := by
    exact (congrArg ((D).boundaryMate Retain) first_germ).trans
      (((D).boundaryMate_involutive Retain (contour.cycle.point j)).trans last_germ.symm)
  have nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots :=
    (A.at_visit 0).1.symm ▸ parent.property
  have below := K.compatibleContourRoofVertex_height_lt_of_nonroot compact nonempty R no_boundary
    level higher M positive inner_disk beta acute w nonroot
  have defect : (D).interiorAngularDefect Set.univ parent.val = 0 :=
    K.compatibleContourSourceOnly_defect_eq_zero_of_no_last_source compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts ends parent.val parent.property
      (fun e h => by
        change (Stack b).getLast? = some e at h
        rw [none_added] at h
        cases h)
  have interior : ¬ (D).IsBoundaryVertex Set.univ parent.val :=
    fun h => parent.property ((Fcut).boundary_roots h)
  rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior] at defect
  have full : (D).totalAngle Retain w = 2 * Real.pi := by
    let wedge (i : Fin (A.length + 1)) := (D).totalAngle Retain
      ((D).boundaryEndVertex Retain (contour.cycle.point (A.visit i)))
    have sum : (∑ i, wedge i) = (D).totalAngle Set.univ parent.val :=
      (D).contourFullParentWedgeRun_sum Selection contour (Fcut).boundary_roots starts parent
    have one : (∑ i, wedge i) = wedge 0 :=
      Finset.sum_eq_single 0 (fun i _ h => (h (only i)).elim) (fun h => (h (Finset.mem_univ _)).elim)
    exact one.symm.trans (sum.trans (sub_eq_zero.mp defect).symm)
  have speed (g : (D).BoundaryEnd Retain)
      (hg : (D).boundaryEndVertex Retain g = (D).boundaryEndVertex Retain s) (t : unitInterval) :
      ENNReal.ofReal (t.val * (D).boundaryBankLength g) =
        edist (Map ((D).directedBoundaryPath g t)) (Map ((D).vertexPoint Retain
          ((D).boundaryEndVertex Retain s))) := by
    rw [← hg, ← (D).directedBoundaryPath_zero g,
      K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W g t 0,
      (T).pairedFolding.edist_directedBoundaryPath_eq_length, mul_comm t.val,
      ENNReal.ofReal_mul ((D).boundaryBankLength_pos g).le, edist_dist]
    congr 1
    apply congrArg ENNReal.ofReal
    change t.val = dist t.val 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  obtain ⟨radius, ⟨original⟩⟩ := (D).exists_directedSlitFanChart Retain s Map speed
    (K.compatibleMesh_corner_fan_chart compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W _ (at_w.symm ▸ below))
  let mark (flag : Bool) (t : unitInterval) := Base b (!flag) t
  let ℓ := (D).boundaryBankLength q
  have mark_names : (fun flag t => Map ((D).directedBoundaryPath
      (if flag then (D).boundaryMate Retain s else s) t)) = mark := by
    funext flag t
    cases flag
    · exact (K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W parent true false t).symm
    · rw [mate]
      exact (K.compatibleContourFiniteRoofGerm_mark compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W parent false false t).symm
  have length_names : (fun flag : Bool => (D).boundaryBankLength
      (if flag then (D).boundaryMate Retain s else s)) = fun _ => ℓ := by
    funext flag
    cases flag
    · change (D).boundaryBankLength s = (D).boundaryBankLength q
      let F := (T).pairedFolding
      have directions := (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
        parent.val parent.property true).trans
        (F.contourParentBank_direction Selection contour (Fcut).boundary_roots starts
          parent.val parent.property false).symm
      exact (F.boundaryBankLength_eq_germDirection_norm s).trans
        ((congrArg norm directions).trans (F.boundaryBankLength_eq_germDirection_norm q).symm)
    · change (D).boundaryBankLength ((D).boundaryMate Retain s) = _
      rw [mate]
  have slab : MarkedSlitFanChart x (2 * Real.pi) mark (fun _ => ℓ) radius := by
    rw [at_w, full, mark_names, length_names] at original
    exact original
  obtain ⟨ε, εpos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover compact nonempty
    R no_boundary level higher M positive inner_disk beta acute contour starts W models geometry a
  have finite (i : Option Event) : {c : Pieces i | Relation.EqvGen Banks a ⟨i, c⟩}.Finite :=
    Set.Subsingleton.finite (by
      intro y hy z hz
      exact eq_of_heq (Sigma.mk.inj ((orbit ⟨i, y⟩ hy).trans (orbit ⟨i, z⟩ hz).symm)).2)
  obtain ⟨δ, δpos, δε, clear⟩ := MetricGluing.exists_bankStack_incident_slot_radius_le Pieces
    Stack Base Gap a finite
    (K.compatibleContourSourceOnlyBaseMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models) εpos cover
  let r := min radius (min δ ℓ)
  have rpos : 0 < r := lt_min slab.positive (lt_min δpos ((D).boundaryBankLength_pos q))
  have rδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have rℓ : r ≤ ℓ := (min_le_right _ _).trans (min_le_right _ _)
  let chart := slab.restrict rpos (min_le_left _ _)
  have finlast : Fin.last (Stack b).length = 0 := by
    apply Fin.ext
    change (Stack b).length = 0
    rw [none_added]
    rfl
  have left (t : unitInterval) : L ⟨b, 0⟩ t = ⟨none, mark true t⟩ :=
    MetricGluing.bankStackLeft_first Pieces Stack Base Gap b t
  have right (t : unitInterval) : Rgt ⟨b, 0⟩ t = ⟨none, mark false t⟩ := by
    rw [← finlast]
    exact MetricGluing.bankStackRight_last Pieces Stack Base Gap b t
  have chart_a : HasMetricBallChart ℂ (Point a) := by
    refine MarkedSlitFanChart.hasMetricBallChart_of_restored_banks Pieces Banks a mark chart
      rℓ ?_ ?_ ?_
    · intro t
      have joined : Banks ⟨none, mark true t⟩ ⟨none, mark false t⟩ :=
        ⟨⟨b, 0⟩, t, (left t).symm, (right t).symm⟩
      exact (MetricGluing.point_eq_of_glue Pieces joined).symm
    · rintro u v ⟨slot, t, hl, hr⟩
      have near : edist (Point a) (Point (L slot t)) < ENNReal.ofReal r := by
        rw [← hl]
        exact ((MetricGluing.edist_of_le Pieces Banks none x u.val).trans_lt
          ((edist_comm _ _).trans_lt u.property))
      obtain ⟨param, related, _⟩ := clear r rpos rδ slot t near
      have label := only_slot ⟨slot, param⟩ (orbit _ related)
      have slot_eq : slot = ⟨b, 0⟩ := congrArg Sigma.fst label
      subst slot
      exact ⟨t, Or.inl ⟨eq_of_heq (Sigma.mk.inj (hl.trans (left t))).2,
        eq_of_heq (Sigma.mk.inj (hr.trans (right t))).2⟩⟩
    · intro z s spos sr near
      obtain ⟨c, joined, close⟩ := cover s spos (sr.trans (rδ.trans δε)) z near
      have same := orbit ⟨z.1, c⟩ joined
      rcases z with ⟨idx, value⟩
      have tag : idx = none := congrArg Sigma.fst same
      subst idx
      have xc : c = x := eq_of_heq (Sigma.mk.inj same).2
      change edist c value < ENNReal.ofReal s at close
      have fit : edist value x < ENNReal.ofReal s := (edist_comm value x).trans_lt (xc ▸ close)
      exact ⟨⟨value, fit.trans_le (ENNReal.ofReal_le_ofReal sr)⟩, rfl, fit⟩
  exact Eq.mp (congrArg (fun z : MetricGluing.Total Pieces => HasMetricBallChart ℂ (Point z))
    (center.symm.trans first_center)) chart_a

end Unfoldings.ConvexRoof
