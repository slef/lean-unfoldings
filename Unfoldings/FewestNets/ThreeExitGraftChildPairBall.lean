module

public import Unfoldings.FewestNets.ThreeExitGraftChildPairClasses
public import Unfoldings.Cone.SectorPairConstruction
public import Unfoldings.Cone.SectorPairBankStack
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

local instance graftChildPairBallIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

private theorem saved_angles_agree
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e f : Event) (he : e ∈ Stack FiniteBank[v,nonroot]) (hf : f ∈ Stack FiniteBank[v,nonroot])
    (pe : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (pf : f ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot]) :
    let p := (Fcut).parents.parent v
    AngleAt[e,IndexAt[p,parent_nonroot,e,pe]] = AngleAt[f,IndexAt[p,parent_nonroot,f,pf]] := by
  let p := (Fcut).parents.parent v
  exact (Fcut).contourSourceBankFanAngle_eq_of_child S.contour S.starts v nonroot e f
    IndexAt[p,parent_nonroot,e,pe] IndexAt[p,parent_nonroot,f,pf]
    (((D).mem_contourSavedGapStack Selection S.contour v e).mp he)
    (((D).mem_contourSavedGapStack Selection S.contour v f).mp hf)
    ((D).contourGapBankIndex_original Selection S.contour p parent_nonroot e _)
    ((D).contourGapBankIndex_original Selection S.contour p parent_nonroot f _)

private theorem stack_adjacent_ne
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    {e f : Event} {before after : List Event}
    (consecutive : Stack FiniteBank[v,nonroot] = before ++ e :: f :: after) : e ≠ f := by
  have nodup : (Stack FiniteBank[v,nonroot]).Nodup :=
    (D).contourSavedGapStack_nodup Selection S.contour v
  have suffix : (e :: f :: after).Nodup :=
    (List.nodup_append.mp (consecutive ▸ nodup)).2.1
  intro same
  exact (List.nodup_cons.mp suffix).1 (same ▸ List.mem_cons_self)

set_option maxHeartbeats 2500000 in
-- Each chart has its own dependent event index and calibrated original sector width.
private theorem exists_child_pair_sector_chart
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e f : Event) (different : e ≠ f)
    (he : e ∈ Stack FiniteBank[v,nonroot]) (hf : f ∈ Stack FiniteBank[v,nonroot])
    (pe : e ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (pf : f ∈ Stack FiniteBank[(Fcut).parents.parent v,parent_nonroot])
    (strict : ∀ (g : Event) (k : Fin LengthAt[g]), let B := BankAt[g]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ))
    {window : ℝ} (window_pos : 0 < window) :
    let p := (Fcut).parents.parent v
    let θ := AngleAt[e,IndexAt[p,parent_nonroot,e,pe]]
    let length (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[p,parent_nonroot]
    let a : Bool → MetricGluing.Total Pieces
      | false => ⟨some e, Gap FiniteBank[p,parent_nonroot] e pe true 0⟩
      | true => ⟨some f, Gap FiniteBank[p,parent_nonroot] f pf false 0⟩
    let mark (b ray : Bool) (t : unitInterval) : Pieces (a b).1 :=
      match b with
      | false => if ray then Gap FiniteBank[v,nonroot] e he true (unitInterval.symm t)
          else Gap FiniteBank[p,parent_nonroot] e pe true t
      | true => if ray then Gap FiniteBank[v,nonroot] f hf false (unitInterval.symm t)
          else Gap FiniteBank[p,parent_nonroot] f pf false t
    ∃ (pos : 0 < θ) (small : θ < 2 * Real.pi) (ρ : ℝ),
      ρ ≤ window ∧ (∀ ray, ρ ≤ length ray) ∧
      ∃ A : MetricGluing.SectorPairChart Pieces a pos small ρ,
        (∀ (b ray : Bool) (t : unitInterval),
          edist (mark b ray t) (a b).2 = ENNReal.ofReal (t.val * length ray)) ∧
        ∀ (b ray : Bool) (t : unitInterval)
          (near : edist (mark b ray t) (a b).2 < ENNReal.ofReal ρ),
          (A.chart b ⟨mark b ray t, near⟩).val.val =
            MetricGluing.SectorPairChart.bankRay θ ray (t.val * length ray) := by
  let p := (Fcut).parents.parent v
  let θ := AngleAt[e,IndexAt[p,parent_nonroot,e,pe]]
  let κ := 2 * Real.pi - θ
  let length (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[p,parent_nonroot]
  let a : Bool → MetricGluing.Total Pieces
    | false => ⟨some e, Gap FiniteBank[p,parent_nonroot] e pe true 0⟩
    | true => ⟨some f, Gap FiniteBank[p,parent_nonroot] f pf false 0⟩
  let mark (b ray : Bool) (t : unitInterval) : Pieces (a b).1 :=
    match b with
    | false => if ray then Gap FiniteBank[v,nonroot] e he true (unitInterval.symm t)
        else Gap FiniteBank[p,parent_nonroot] e pe true t
    | true => if ray then Gap FiniteBank[v,nonroot] f hf false (unitInterval.symm t)
        else Gap FiniteBank[p,parent_nonroot] f pf false t
  obtain ⟨θpos, r₀, r₀pos, left, left_center, left_ray⟩ :=
    L.contourGraftGap_parent_bend_marked_chart S
      v nonroot parent_nonroot e he pe (strict e) true
  let RightSpec (w : ℝ) : Prop :=
    ∃ (p : 0 < w) (r : ℝ) (rpos : 0 < r)
      (B : Metric.eball (a true).2 (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin p.le) (ENNReal.ofReal r)),
      (B ⟨(a true).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
        closedAngularSectorOrigin p.le ∧
      ∀ (ray : Bool) (t : unitInterval)
        (near : edist (mark true ray t) (a true).2 < ENNReal.ofReal r),
        (B ⟨mark true ray t, near⟩).val.val =
          if ray = false then (t.val * length ray) • polarRay w else ((t.val * length ray : ℝ) : ℂ)
  let w := AngleAt[f,IndexAt[p,parent_nonroot,f,pf]]
  have saved := saved_angles_agree S v nonroot parent_nonroot e f he hf pe pf
  have width_match : 2 * Real.pi - w = κ := congrArg (2 * Real.pi - ·) saved.symm
  have right_chart : RightSpec (2 * Real.pi - w) :=
    L.contourGraftGap_parent_bend_marked_chart S
      v nonroot parent_nonroot f hf pf (strict f) false
  obtain ⟨κpos, r₁, r₁pos, right, right_center, right_ray⟩ :=
    Eq.mp (congrArg RightSpec width_match) right_chart
  have small : θ < 2 * Real.pi := sub_pos.mp κpos
  have balance : θ + κ = 2 * Real.pi := by dsimp [κ]; ring
  have length_pos (ray : Bool) : 0 < length ray := by
    cases ray <;> exact (D).boundaryBankLength_pos _
  let ρ := min (min r₀ r₁) (min (min (length false) (length true)) window)
  have ρpos : 0 < ρ :=
    lt_min (lt_min r₀pos r₁pos) (lt_min (lt_min (length_pos false) (length_pos true)) window_pos)
  have ρ₀ : ρ ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have ρ₁ : ρ ≤ r₁ := (min_le_left _ _).trans (min_le_right _ _)
  have ρ_window : ρ ≤ window := (min_le_right _ _).trans (min_le_right _ _)
  have ρ_len (ray : Bool) : ρ ≤ length ray := by
    apply (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
    cases ray
    · exact min_le_left _ _
    · exact min_le_right _ _
  have distinct : (a false).1 ≠ (a true).1 := fun h => different (Option.some.inj h)
  let A := MetricGluing.SectorPairChart.fromSectors a θpos small κpos balance
    r₀pos r₁pos ρpos ρ₀ ρ₁ left right left_center right_center distinct
  refine ⟨θpos, small, ρ, ρ_window, ρ_len, A, ?_, ?_⟩
  · intro b ray t
    cases b
    · exact L.contourGraftGap_parent_bend_distance S
        v nonroot parent_nonroot e he pe true ray t
    · exact L.contourGraftGap_parent_bend_distance S
        v nonroot parent_nonroot f hf pf false ray t
  · intro b ray t near
    let s := t.val * length ray
    cases b
    · have close := near.trans_le (ENNReal.ofReal_le_ofReal ρ₀)
      change (left ⟨mark false ray t, close⟩).val.val =
        MetricGluing.SectorPairChart.bankRay θ ray s
      refine (left_ray ray t close).trans ?_
      cases ray
      · rfl
      · exact Complex.real_smul
    · have close := near.trans_le (ENNReal.ofReal_le_ofReal ρ₁)
      let turn := rotation (Circle.exp θ)
      change turn (right ⟨mark true ray t, close⟩).val.val =
        MetricGluing.SectorPairChart.bankRay θ ray s
      refine (congrArg turn (right_ray ray t close)).trans ?_
      cases ray
      · change polarRay θ * (s • polarRay κ) = (s : ℂ)
        rw [Complex.real_smul, mul_left_comm, ← polarRay_add, balance]
        simp [polarRay]
      · exact mul_comm _ _

set_option maxHeartbeats 250000 in
-- Seam and ball covers keep their original dependent slot and piece types.
/-- At the same-child junction between consecutive inserted gaps, the actual
source-only graft has a whole planar ball at their common bend. -/
theorem contourGraftChildPair_planarBall
    (v : (D).Vertex Set.univ) (nonroot : v ∉ (Fcut).parents.roots)
    (parent_nonroot : (Fcut).parents.parent v ∉ (Fcut).parents.roots)
    (e f : Event) (before after : List Event)
    (consecutive : Stack FiniteBank[v,nonroot] = before ++ e :: f :: after)
    (strict : ∀ (g : Event) (k : Fin LengthAt[g]), let B := BankAt[g]
      0 < inner ℝ (B.chain.vertex k.succ.castSucc - B.start) (B.chain.edge k.succ)) :
    let parent := FiniteBank[(Fcut).parents.parent v,parent_nonroot]
    ∃ i : Fin ((Stack parent).length + 1),
      Named false ⟨parent, i⟩ 0 = ⟨parent, some e, true, 0⟩ ∧
      Named true ⟨parent, i⟩ 0 = ⟨parent, some f, false, 0⟩ ∧
      HasMetricBallChart ℂ (MetricGluing.point Pieces Banks (Left ⟨parent, i⟩ 0)) := by
  let (a : Attachment) : TopologicalSpace (Param a) :=
    (contourAttachmentMetric S a).toUniformSpace.toTopologicalSpace
  let p := (Fcut).parents.parent v
  let ch := FiniteBank[v,nonroot]
  let pa := FiniteBank[p,parent_nonroot]
  obtain ⟨i, j, class_eq, recovery, le, rf, le', rf'⟩ :=
    L.contourGraftChildPair_class S v nonroot parent_nonroot e f
      (geometry e) (geometry f) before after consecutive
  let first : Time := ⟨⟨pa, i⟩, 0⟩
  let second : Time := ⟨⟨ch, j⟩, 1⟩
  have he : e ∈ Stack ch := show Valid ⟨ch, some e, true, 1⟩ from
    le' ▸ MetricGluing.bankStackEndpointAddress_valid Stack false second.1 second.2
  have hf : f ∈ Stack ch := show Valid ⟨ch, some f, false, 1⟩ from
    rf' ▸ MetricGluing.bankStackEndpointAddress_valid Stack true second.1 second.2
  have pe : e ∈ Stack pa := show Valid ⟨pa, some e, true, 0⟩ from
    le ▸ MetricGluing.bankStackEndpointAddress_valid Stack false first.1 first.2
  have pf : f ∈ Stack pa := show Valid ⟨pa, some f, false, 0⟩ from
    rf ▸ MetricGluing.bankStackEndpointAddress_valid Stack true first.1 first.2
  let a : Bool → MetricGluing.Total Pieces
    | false => ⟨some e, Gap pa e pe true 0⟩
    | true => ⟨some f, Gap pa f pf false 0⟩
  let mark (b ray : Bool) (t : unitInterval) : Pieces (a b).1 :=
    match b with
    | false => if ray then Gap ch e he true (unitInterval.symm t) else Gap pa e pe true t
    | true => if ray then Gap ch f hf false (unitInterval.symm t) else Gap pa f pf false t
  let seamTime (ray : Bool) (t : unitInterval) : Time :=
    if ray then ⟨second.1, unitInterval.symm t⟩ else ⟨first.1, t⟩
  have namedAt (b : Bool) (q : Time) (u : Param q.1.1) (g : Event) (mem : g ∈ Stack q.1.1)
      (side : Bool) (named : Named b q.1 q.2 = ⟨q.1.1, some g, side, q.2⟩) :
      EndAt b q.1 u = ⟨some g, Gap q.1.1 g mem side u⟩ :=
    MetricGluing.bankStackEndpoint_eq_of_gap_address Stack Pieces Base Gap b ⟨q.1, u⟩
      q.1.1 g mem side u
      (MetricGluing.bankStackEndpointAddress_at_time Stack b q.1 q.2 u g side named)
  have seam_ends (b ray : Bool) (t : unitInterval) :
      EndAt b (seamTime ray t).1 (seamTime ray t).2 = ⟨(a b).1, mark b ray t⟩ := by
    cases b <;> cases ray
    · exact namedAt false first t e pe true le
    · exact namedAt false second (unitInterval.symm t) e he true le'
    · exact namedAt true first t f pf false rf
    · exact namedAt true second (unitInterval.symm t) f hf false rf'
  have lc : Left first.1 first.2 = a false := namedAt false first 0 e pe true le
  have rc : Right first.1 first.2 = a true := namedAt true first 0 f pf false rf
  let point := MetricGluing.point Pieces Banks
  obtain ⟨ε, εpos, cover⟩ := L.contourGraft_piece_ball_cover S (Left first.1 first.2)
  obtain ⟨δ, δpos, slots⟩ := MetricGluing.bankStack_exists_near_two_slots
    (Parameter := Param) Stack Pieces Base Gap
    first second (fun z => (class_eq z).mp) recovery
    (L.isClosedEmbedding_contourBaseMark S)
    (isClosedEmbedding_contourGapMark S)
    εpos cover
  have different : e ≠ f := stack_adjacent_ne S v nonroot consecutive
  obtain ⟨pos, small, ρ, fit, length_fit, A, distance, coords⟩ :=
    exists_child_pair_sector_chart L S v nonroot parent_nonroot
      e f different he hf pe pf strict (lt_min εpos δpos)
  have fit_ε : ρ ≤ ε := fit.trans (min_le_left _ _)
  have fit_δ : ρ ≤ δ := fit.trans (min_le_right _ _)
  let length (ray : Bool) := if ray then BankLength[v,nonroot] else BankLength[p,parent_nonroot]
  have named_slots (q : Time)
      (near : edist (point (Left first.1 first.2)) (point (Left q.1 q.2)) < ENNReal.ofReal ρ) :
      ∃ ray t, q = seamTime ray t :=
    MetricGluing.bankStack_exists_named_time (Parameter := Param) Stack
      first.1 second.1 (Equiv.refl unitInterval) unitInterval.symmHomeomorph.toEquiv q
      (slots q.1 q.2 (near.trans_le (ENNReal.ofReal_le_ofReal fit_δ)))
  refine ⟨i, le, rf, ?_⟩
  exact A.bankStack_planarBall Pieces Stack Base Gap first lc rc mark seamTime seam_ends
    length length_fit distance coords named_slots fit_ε (fun z => (class_eq z).mp) cover

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
