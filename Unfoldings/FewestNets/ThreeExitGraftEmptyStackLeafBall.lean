module

public import Unfoldings.FewestNets.ThreeExitGraftEmptyStackClass
public import Unfoldings.Cone.DirectedSlitChart
public import Unfoldings.Cone.MarkedSlitRestoration
public import Unfoldings.Metric.BankStackIncidentSlots
public import Unfoldings.FewestNets.ThreeExitGraftVertexRadii
public import Unfoldings.FewestNets.ThreeExitRoofSectorGerms
public import Unfoldings.FewestNets.ThreeExitGraftBendMarks
public import Unfoldings.FewestNets.ThreeExitGraftLabels
public import Unfoldings.Roof.PotentialContourJunctionAngles
public import Unfoldings.FewestNets.ThreeExitGraftRoofRun

/-! The original sectors glue to full planar balls at finite vertices. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 1800000

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftEmptyStackLeafBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Map" => L.fineMeshWholeMap S.higher
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle S.contour) j)))) :
      MetricGluing.Total Pieces)
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection S.contour (PotentialCutForest.boundary_roots Fcut) S.starts v h
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := Param) Stack
local notation "Germ" => contourFiniteRoofGerm S
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "SourceEdge[" e "]" => (Sum.inl (Subtype.mk SourceOf[e]
  (TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e)) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Point" => MetricGluing.point Pieces Banks
local notation "geometry" => S.gaps

local notation "Child" => Edge
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection S.contour e
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection S.contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection S.contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection S.contour v e) member))
local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection S.contour (PotentialCutForest.boundary_roots Fcut)
    S.starts v h false)
local notation "AngleAt[" e "," i "]" => PotentialCutForest.contourSourceBankFanAngle Fcut S.contour S.starts e i
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "RoofSite" => Edge × Bool × Bool
local notation "SiteTime" => contourGraftRoofSiteTime S
local notation "AtSite[" a "]" => Germ (Prod.fst a) (Prod.fst (Prod.snd a))
  (Prod.snd (Prod.snd a))
local notation "NamedSlot" => (Σ e : Edge,
  Fin (List.length (Stack FiniteBank[Subtype.val e,Subtype.property e]) + 1) × Bool)
local notation "Defect[" v "]" => TriangleComplex.interiorAngularDefect D Set.univ v

set_option maxHeartbeats 3200000 in
-- The incidence tests carry the dependent types of the actual roof marks.
/-- The only roof copy at an empty-stack leaf is a full-turn slit.
Restoring its original outgoing bank gives a planar ball. -/
theorem contourGraftEmptyStack_leaf_planarBall
    (ends : (D).contourOriginalVertex Selection S.contour (Fin.last S.contour.length) ∈
      (Fcut).parents.roots)
    (parent : Edge) (none_added : Stack FiniteBank[parent.val,parent.property] = [])
    (leaf : ((D).contourFullParentWedgeRun Selection S.contour
      (Fcut).boundary_roots S.starts parent).length = 0) :
    HasMetricBallChart ℂ (Point (EndAt true ⟨FiniteBank[parent.val,parent.property], 0⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  let b := FiniteBank[parent.val,parent.property]
  let A := (D).contourFullParentWedgeRun Selection S.contour (Fcut).boundary_roots S.starts parent
  obtain ⟨H, first_center, roof_center, route, _, _, _⟩ :=
    L.exists_contourGraftEmptyStackClass S parent none_added
  let j := A.visit 0
  let w := (D).boundaryEndVertex Retain (S.contour.cycle.point j)
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
  have only_slot (s : Time) (haz : Left s.1 s.2 = a) : s = ⟨⟨b, 0⟩, 0⟩ := by
    obtain ⟨i, hi⟩ := H.incident 0 false s (haz.trans center.symm)
    rw [hi, route, show i = Fin.last A.length from (only i).trans (only _).symm,
      MetricGluing.BankStackCyclicClass.roofTime_last]
  have first_germ : Germ parent true false = (D).boundaryMate Retain (S.contour.cycle.point j) :=
    ((D).contourParent_firstVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans
      (congrArg (fun i => (D).boundaryMate Retain (S.contour.cycle.point i)) A.at_first.symm)
  have last_germ : Germ parent false false = S.contour.cycle.point j := by
    have h := ((D).contourParent_lastVisit_germ Selection S.contour (Fcut).boundary_roots S.starts
      parent.val parent.property).symm.trans (congrArg S.contour.cycle.point A.at_last.symm)
    rw [only (Fin.last A.length)] at h
    exact h
  let s := Germ parent true false
  let q := Germ parent false false
  have at_w : (D).boundaryEndVertex Retain s = w :=
    ((D).boundaryEnd_vertex_eq_iff Retain _ _).mpr (Or.inr first_germ)
  have mate : (D).boundaryMate Retain s = q := by
    exact (congrArg ((D).boundaryMate Retain) first_germ).trans
      (((D).boundaryMate_involutive Retain (S.contour.cycle.point j)).trans last_germ.symm)
  have nonroot : (D).contourOriginalVertex Selection S.contour j ∉ (Fcut).parents.roots :=
    (A.at_visit 0).1.symm ▸ parent.property
  have defect : (D).interiorAngularDefect Set.univ parent.val = 0 :=
    (Fcut).contourGraft_defect_eq_zero_of_no_last_source S.contour S.starts ends parent.val parent.property
      (fun e h => by
        change (Stack b).getLast? = some e at h
        rw [none_added] at h
        cases h)
  have interior : ¬ (D).IsBoundaryVertex Set.univ parent.val :=
    fun h => parent.property ((Fcut).boundary_roots h)
  rw [TriangleComplex.interiorAngularDefect, ite_eq_right interior] at defect
  have full : (D).totalAngle Retain w = 2 * Real.pi := by
    let wedge (i : Fin (A.length + 1)) := (D).totalAngle Retain
      ((D).boundaryEndVertex Retain (S.contour.cycle.point (A.visit i)))
    have sum : (∑ i, wedge i) = (D).totalAngle Set.univ parent.val :=
      (D).contourFullParentWedgeRun_sum Selection S.contour (Fcut).boundary_roots S.starts parent
    have one : (∑ i, wedge i) = wedge 0 :=
      Finset.sum_eq_single 0 (fun i _ h => (h (only i)).elim) (fun h => (h (Finset.mem_univ _)).elim)
    exact one.symm.trans (sum.trans (sub_eq_zero.mp defect).symm)
  have speed (g : (D).BoundaryEnd Retain)
      (hg : (D).boundaryEndVertex Retain g = (D).boundaryEndVertex Retain s) (t : unitInterval) :
      ENNReal.ofReal (t.val * (D).boundaryBankLength g) =
        edist (Map ((D).directedBoundaryPath g t)) (Map ((D).vertexPoint Retain
          ((D).boundaryEndVertex Retain s))) := by
    rw [← hg, ← (D).directedBoundaryPath_zero g,
      L.fineMeshWholeMap_edist_bank S.higher g t 0,
      (T).pairedFolding.edist_directedBoundaryPath_eq_length, mul_comm t.val,
      ENNReal.ofReal_mul ((D).boundaryBankLength_pos g).le, edist_dist]
    congr 1
    apply congrArg ENNReal.ofReal
    change t.val = dist t.val 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  obtain ⟨radius, ⟨original⟩⟩ := (D).exists_directedSlitFanChart Retain s Map speed
    (L.contourCutVertex_tangent_chart S _ (at_w.symm ▸ nonroot))
  let mark (flag : Bool) (t : unitInterval) := Base b (!flag) t
  let ℓ := (D).boundaryBankLength q
  have mark_names : (fun flag t => Map ((D).directedBoundaryPath
      (if flag then (D).boundaryMate Retain s else s) t)) = mark := by
    funext flag t
    cases flag
    · exact (L.contourFiniteRoofGerm_mark S parent true false t).symm
    · rw [mate]
      exact (L.contourFiniteRoofGerm_mark S parent false false t).symm
  have length_names : (fun flag : Bool => (D).boundaryBankLength
      (if flag then (D).boundaryMate Retain s else s)) = fun _ => ℓ := by
    funext flag
    cases flag
    · change (D).boundaryBankLength s = (D).boundaryBankLength q
      let F := (T).pairedFolding
      have directions := (F.contourParentBank_direction Selection S.contour (Fcut).boundary_roots S.starts
        parent.val parent.property true).trans
        (F.contourParentBank_direction Selection S.contour (Fcut).boundary_roots S.starts
          parent.val parent.property false).symm
      exact (F.boundaryBankLength_eq_germDirection_norm s).trans
        ((congrArg norm directions).trans (F.boundaryBankLength_eq_germDirection_norm q).symm)
    · change (D).boundaryBankLength ((D).boundaryMate Retain s) = _
      rw [mate]
  have slab : MarkedSlitFanChart x (2 * Real.pi) mark (fun _ => ℓ) radius := by
    rw [at_w, full, mark_names, length_names] at original
    exact original
  obtain ⟨ε, εpos, cover⟩ := L.contourGraft_piece_ball_cover S a
  have finite (i : Option Event) : {c : Pieces i | Relation.EqvGen Banks a ⟨i, c⟩}.Finite :=
    Set.Subsingleton.finite (by
      intro y hy z hz
      exact eq_of_heq (Sigma.mk.inj ((orbit ⟨i, y⟩ hy).trans (orbit ⟨i, z⟩ hz).symm)).2)
  obtain ⟨δ, δpos, δε, clear⟩ := MetricGluing.exists_bankStack_incident_slot_radius_le Pieces
    Stack Base Gap a finite
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S) εpos cover
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
  have left (t : unitInterval) : Left ⟨b, 0⟩ t = ⟨none, mark true t⟩ :=
    MetricGluing.bankStackLeft_first Pieces Stack Base Gap b t
  have right (t : unitInterval) : Right ⟨b, 0⟩ t = ⟨none, mark false t⟩ := by
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
      have near : edist (Point a) (Point (Left slot t)) < ENNReal.ofReal r := by
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

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
