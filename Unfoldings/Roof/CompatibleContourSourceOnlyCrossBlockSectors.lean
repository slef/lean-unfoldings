module

public import Unfoldings.Cone.PlacedAngularSectorChart
public import Unfoldings.Roof.CompatibleContourSourceOnlyBendMarks
public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockAngles
public import Unfoldings.Roof.CompatibleContourSourceOnlyCrossBlockClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofWedgeChart

/-! The normalized angular sectors in the actual cross-block seam class. -/

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

local instance sourceOnlyCrossBlockSectorsIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyCrossBlockSectorsWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))
local notation "AngleAt[" e "," j "]" => K.compatibleContourSourceBankFanAngle compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e j

private theorem gap_bend_sector_at_parent
    (child parent : Edge) (parent_eq : (Fcut).parents.parent child.val = parent.val)
    (e : Event) (here : e ∈ Stack FiniteBank[child.val,child.property])
    (above : e ∈ Stack FiniteBank[parent.val,parent.property])
    (strict : ∀ k : Fin LengthAt[e], let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (side : Bool) :
    let saved := AngleAt[e,IndexAt[parent.val,parent.property,e,above]]
    let angle := if side then saved else 2 * Real.pi - saved
    Nonempty (CenteredSectorGerm (Gap FiniteBank[parent.val,parent.property] e above side 0) angle) := by
  obtain ⟨parent, nonroot⟩ := parent
  change (Fcut).parents.parent child.val = parent at parent_eq
  subst parent
  obtain ⟨pos, r, rpos, chart, centered, _⟩ :=
    K.compatibleContourSourceOnlyGap_parent_bend_marked_chart compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts geometry child.val child.property
      nonroot e here above strict side
  exact ⟨⟨pos, r, rpos, chart, centered⟩⟩

private theorem roof_wedge_centered_sector
    (old_child new_child : Edge) (j : Fin (contour.length + 1))
    (after_old : finRotate (contour.length + 1) (Interval[old_child.val,old_child.property]).leave = j)
    (before_new : (Interval[new_child.val,new_child.property]).enter = j)
    (nonroot : (D).contourOriginalVertex Selection contour j ∉ (Fcut).parents.roots) :
    let q := (D).boundaryEndVertex Retain (contour.cycle.point j)
    Nonempty (CenteredSectorGerm (Map ((D).vertexPoint Retain q)) ((D).totalAngle Retain q)) := by
  let q := (D).boundaryEndVertex Retain (contour.cycle.point j)
  let x := Map ((D).vertexPoint Retain q)
  obtain ⟨_, r, rpos, chart, first, _⟩ := K.compatibleContourSourceOnlyRoofWedge_sector_chart
    compact nonempty R no_boundary level higher M positive inner_disk beta acute
      contour starts W old_child new_child j after_old before_new nonroot
  have base : Base (.inl old_child) false 1 = x :=
    (K.compatibleContourSourceOnlyRoofWedge_baseMark_iff compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W old_child new_child j after_old
      before_new nonroot (.inl old_child) false 1).mpr (Or.inl ⟨rfl, rfl⟩)
  have near : edist (Base (.inl old_child) false 1) x < ENNReal.ofReal r :=
    (congrArg (edist · x) base).trans_lt ((edist_self x).trans_lt (ENNReal.ofReal_pos.mpr rpos))
  have output := first 1 near
  have pts : (⟨Base (.inl old_child) false 1, near⟩ : Metric.eball x (ENNReal.ofReal r)) =
      ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ := Subtype.ext base
  have centered : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
      closedAngularSectorOrigin ((D).totalAngle_pos Retain q).le := by
    apply PolygonalPoint.ext
    rw [← pts]
    exact output.trans (by norm_num [closedAngularSectorOrigin])
  exact ⟨⟨(D).totalAngle_pos Retain q, r, rpos, chart, centered⟩⟩

/-- The exact cross-block cyclic class has a whole original sector chart at every
center. Its sectors have positive angles and add to one full turn. -/
theorem exists_compatibleContourSourceOnlyCrossBlockSectors
    (parent old_child new_child : Edge)
    (old_parent : (Fcut).parents.parent old_child.val = parent.val)
    (new_parent : (Fcut).parents.parent new_child.val = parent.val)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : (Fcut).parents.Ancestor SourceOf[old] old_child.val)
    (new_in : (Fcut).parents.Ancestor SourceOf[new] new_child.val)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (pre post : List Event)
    (adjacent : Stack FiniteBank[parent.val,parent.property] = pre ++ new :: old :: post) :
    let above := FiniteBank[parent.val,parent.property]
    ∃ (n : ℕ) (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (n + 2))
      (slot : Fin ((Stack above).length + 1)) (angle : Fin (n + 3) → ℝ),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      H.center 0 = EndAt true ⟨above, slot⟩ 0 ∧
      Function.Injective H.center ∧
      (∑ i, angle i) = 2 * Real.pi ∧
      ∀ i, Nonempty (CenteredSectorGerm (H.center i).2 (angle i)) := by
  obtain ⟨A, H, slot, new_out, old_out, first_center, last_center, roof_center, _, _, _,
      interval, unique⟩ :=
    K.exists_compatibleContourSourceOnlyCrossBlockData compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models parent old_child new_child old_parent
      new_parent different old new old_in new_in (geometry old) (geometry new) pre post adjacent
  let above := FiniteBank[parent.val,parent.property]
  let closing : Time := ⟨⟨above, slot⟩, 0⟩
  have old_member : old ∈ Stack above := show Valid ⟨above, some old, false, 0⟩ from
    old_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack true closing.1 closing.2
  have new_member : new ∈ Stack above := show Valid ⟨above, some new, true, 0⟩ from
    new_out ▸ MetricGluing.bankStackEndpointAddress_valid Stack false closing.1 closing.2
  have old_here : old ∈ Stack FiniteBank[old_child.val,old_child.property] :=
    ((D).mem_contourSavedGapStack Selection contour old_child.val old).mpr old_in
  have new_here : new ∈ Stack FiniteBank[new_child.val,new_child.property] :=
    ((D).mem_contourSavedGapStack Selection contour new_child.val new).mpr new_in
  let left := 2 * Real.pi - AngleAt[old,IndexAt[parent.val,parent.property,old,old_member]]
  let right := AngleAt[new,IndexAt[parent.val,parent.property,new,new_member]]
  let wedge (i : Fin (A.length + 1)) := (D).totalAngle Retain
    ((D).boundaryEndVertex Retain (contour.cycle.point (A.visit i)))
  let middle (j : Fin (A.length + 2)) : ℝ := Fin.lastCases right wedge j
  let angle (i : Fin (A.length + 3)) : ℝ := Fin.cases left middle i
  have ordered : old.val.val ≤ new.val.val := by
    have sorted : (Stack above).Pairwise (fun a b => b.val.val < a.val.val) :=
      ((D).contourEdgeGapStack_ordered Selection contour parent.val).reverse
    rw [adjacent] at sorted
    have ranked := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 old
      List.mem_cons_self
    exact ranked.le
  have balance : left + (∑ i, wedge i) + right = 2 * Real.pi :=
    K.compatibleContourSourceOnlyCrossBlock_angle_balance compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts parent.val parent.property old new
      old_member new_member ordered _ _ A interval
  have angle_last : angle (Fin.last (A.length + 1)).succ = right := by
    change middle (Fin.last (A.length + 1)) = right
    exact Fin.lastCases_last
  have angle_roof (i : Fin (A.length + 1)) : angle i.castSucc.succ = wedge i := by
    change middle i.castSucc = wedge i
    exact Fin.lastCases_castSucc i
  have full : (∑ i, angle i) = 2 * Real.pi := by
    rw [Fin.sum_univ_succ]
    change left + (∑ i, middle i) = 2 * Real.pi
    rw [Fin.sum_univ_castSucc]
    have first : (∑ i : Fin (A.length + 1), middle i.castSucc) = ∑ i, wedge i := by
      exact Finset.sum_congr rfl (fun i _ => Fin.lastCases_castSucc i)
    rw [first, show middle (Fin.last (A.length + 1)) = right from Fin.lastCases_last]
    linarith
  refine ⟨A.length, H, slot, angle, new_out, old_out, first_center, unique, full, ?_⟩
  let P (a : MetricGluing.Total Pieces) (θ : ℝ) := Nonempty (CenteredSectorGerm a.2 θ)
  have left_center : H.center 0 = ⟨some old, Gap above old old_member false 0⟩ :=
    first_center.trans (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      true closing above old old_member false 0 old_out)
  have right_center : H.center (Fin.last (A.length + 1)).succ =
      ⟨some new, Gap above new new_member true 0⟩ := by
    rw [Fin.succ_last]
    exact last_center.trans (MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap
      false closing above new new_member true 0 new_out)
  have old_sector : P ⟨some old, Gap above old old_member false 0⟩ left :=
    gap_bend_sector_at_parent K compact nonempty R no_boundary level higher M positive inner_disk
      beta acute contour starts geometry old_child parent old_parent old old_here old_member
      (strict old) false
  have new_sector : P ⟨some new, Gap above new new_member true 0⟩ right :=
    gap_bend_sector_at_parent K compact nonempty R no_boundary level higher M positive inner_disk
      beta acute contour starts geometry new_child parent new_parent new new_here new_member
      (strict new) true
  intro i
  change P (H.center i) (angle i)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact left_center.symm ▸ old_sector
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [angle_last]
      exact right_center.symm ▸ new_sector
    · rw [angle_roof k]
      have nonroot : (D).contourOriginalVertex Selection contour (A.visit k) ∉ (Fcut).parents.roots :=
        (A.at_visit k).1.symm ▸ parent.property
      have geom : P RoofPoint[A.visit k] (wedge k) :=
        roof_wedge_centered_sector K compact nonempty R no_boundary level higher M positive inner_disk
          beta acute contour starts W (A.previous old_child k) (A.following new_child k) (A.visit k)
          (A.previous_returns old_child rfl k) (A.following_enters new_child rfl k) nonroot
      exact (roof_center k).symm ▸ geom

/-- Place all original cross-block sectors at one radius, with the two gap
charts reflected to follow the same cyclic order as the roof wedges. -/
theorem exists_compatibleContourSourceOnlyPlacedCrossBlockSectors
    (parent old_child new_child : Edge)
    (old_parent : (Fcut).parents.parent old_child.val = parent.val)
    (new_parent : (Fcut).parents.parent new_child.val = parent.val)
    (different : old_child.val ≠ new_child.val) (old new : Event)
    (old_in : (Fcut).parents.Ancestor SourceOf[old] old_child.val)
    (new_in : (Fcut).parents.Ancestor SourceOf[new] new_child.val)
    (strict : ∀ (e : Event) (k : Fin LengthAt[e]), let B := BankAt[e]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    (pre post : List Event)
    (adjacent : Stack FiniteBank[parent.val,parent.property] = pre ++ new :: old :: post)
    {limit : ℝ} (limit_pos : 0 < limit) :
    let above := FiniteBank[parent.val,parent.property]
    ∃ (n : ℕ) (H : MetricGluing.BankStackCyclicClass Pieces Stack Base Gap (n + 2))
      (slot : Fin ((Stack above).length + 1)) (heading : Fin (n + 4) → ℝ),
      Named false ⟨above, slot⟩ 0 = ⟨above, some new, true, 0⟩ ∧
      Named true ⟨above, slot⟩ 0 = ⟨above, some old, false, 0⟩ ∧
      H.center 0 = EndAt true ⟨above, slot⟩ 0 ∧
      StrictMono heading ∧ heading 0 = 0 ∧ heading (Fin.last (n + 3)) = 2 * Real.pi ∧
      ∃ ρ, 0 < ρ ∧ ρ ≤ limit ∧ ∃ origin : ∀ j, PolygonalPoint (placedAngularSector heading j),
        Nonempty (MetricGluing.SectorCoverChart Pieces H.center (placedAngularSector heading)
          origin ρ) := by
  obtain ⟨n, H, slot, angle, new_out, old_out, at_center, distinct, total, sectors⟩ :=
    K.exists_compatibleContourSourceOnlyCrossBlockSectors compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W geometry parent old_child new_child
      old_parent new_parent different old new old_in new_in strict pre post adjacent
  let heading : Fin (n + 4) → ℝ := Fin.partialSum angle
  have same (i : Fin (n + 3)) : heading i.succ - heading i.castSucc = angle i := by
    change Fin.partialSum angle i.succ - _ = _
    rw [Fin.partialSum_succ]
    ring
  let charts (i : Fin (n + 3)) : CenteredSectorGerm (H.center i).2
      (heading i.succ - heading i.castSucc) :=
    (same i).symm ▸ Classical.choice (sectors i)
  have mono : StrictMono heading := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact sub_pos.mp (charts i).angle_pos
  have full : heading (Fin.last (n + 3)) = 2 * Real.pi := by
    suffices heading (Fin.last (n + 3)) = ∑ i, angle i from this.trans total
    change ((List.ofFn angle).take (n + 3)).sum = _
    rw [List.take_of_length_le (by simp)]
    exact List.sum_ofFn
  let reflected (i : Fin (n + 3)) := decide (i = 0 ∨ i = Fin.last (n + 2))
  obtain ⟨ρ, positive_radius, small, chart⟩ :=
    MetricGluing.SectorCoverChart.exists_of_centered_sectors Pieces heading H.center reflected
      charts distinct limit_pos
  exact ⟨n, H, slot, heading, new_out, old_out, at_center, mono, Fin.partialSum_zero angle,
    full, ρ, positive_radius, small, _, chart⟩

end Unfoldings.ConvexRoof
