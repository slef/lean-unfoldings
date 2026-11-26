module

public import Unfoldings.FewestNets.ThreeExitGraftJoinBall
public import Unfoldings.FewestNets.ThreeExitGraftTerminalFiber
public import Unfoldings.FewestNets.ThreeExitGraftUnmarkedCharts
public import Unfoldings.FewestNets.ThreeExitGraftFiniteSeamCharts
public import Unfoldings.FewestNets.ThreeExitGraftTailSeamCharts
public import Unfoldings.FewestNets.ThreeExitGraftCellCharts
public import Unfoldings.Metric.FlatPlanarCollapse
public import Unfoldings.Metric.BankStackEndpointExistence

/-! Collapsing the full metrically flat graft produces a global isometry. -/

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

local instance graftDevelopmentIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Graft" => contourGraft L S
local notation "Point" => MetricGluing.point Pieces Banks
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Surface" => SpatialEnvelope.wholeSurface M.plane
local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Phys" => contourPhysicalAddress L S
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap

/-- The finite and infinite marked banks exhaust the entire boundary of a gap. -/
theorem exists_contourGraftGapMark_of_frontier (e : Event) (x : Pieces (some e))
    (boundary : x.val ∈ frontier (Model[e]).region) :
    ∃ (a : Attachment) (member : e ∈ Stack a) (side : Bool) (t : Param a),
      Gap a e member side t = x := by
  rw [(Model[e]).frontier_eq] at boundary
  have bank : ∃ side, x.val ∈ ((Model[e]).bank side).carrier := by
    rcases boundary with first | last
    · exact ⟨false, first⟩
    · exact ⟨true, last⟩
  obtain ⟨side, on_bank⟩ := bank
  obtain ⟨address, point_eq⟩ := ((Model[e]).bank side).exists_address on_bank
  obtain ⟨a, member, t, label⟩ := (Fcut).exists_contourGapAddress_eq S.contour e address
  refine ⟨a, member, !side, t, PolygonalPoint.ext ?_⟩
  rw [contourGraftGapMark_eq_intrinsicAddressPoint S, Bool.not_not, label]
  exact point_eq

/-- It remains to check the endpoint sectors of the finite seams. Every other point
of the graft already has a whole planar ball in the same metric. -/
theorem contourGraft_hasMetricBallChart_of_finite_vertices
    (finite_vertex : ∀ (e : Child) (i : Fin ((Stack (.inl e)).length + 1))
      (t : unitInterval), t = 0 ∨ t = 1 →
        HasMetricBallChart ℂ (Point (Left ⟨.inl e, i⟩ t)))
    (z : Graft) : HasMetricBallChart Plane z := by
  let complexPlane := PlanarTopology.complexIsometry.toIsometryEquiv
  have slot_chart (slot : BankStackSlot Stack) (t : Param slot.1) :
      HasMetricBallChart ℂ (Point (Left slot t)) := by
    rcases slot with ⟨e | e, i⟩
    · by_cases zero : t = 0
      · exact finite_vertex e i t (Or.inl zero)
      by_cases one : t = 1
      · exact finite_vertex e i t (Or.inr one)
      exact L.contourGraft_finiteSeam_chart S e i t
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm zero), lt_of_le_of_ne t.property.2 one⟩
    · by_cases zero : t = 0
      · subst t
        exact L.contourGraft_terminalJoin_planarBall S e i
      · exact L.contourGraft_tailSeam_chart S e i t (lt_of_le_of_ne zero_le (Ne.symm zero))
  have addressed (a : Addr) (valid : Valid a) :
      HasMetricBallChart Plane (Point (Mark a valid)) := by
    obtain ⟨side, slot, t, name⟩ := exists_bankStackEndpointAddress_eq Stack a valid
    have equality : Mark a valid = bankStackEndpoint Stack Pieces Base Gap side slot t := by
      cases name
      exact bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot t
    rw [equality]
    apply HasMetricBallChart.modelIsometryEquiv _ complexPlane
    cases side
    · exact slot_chart slot t
    · have glued : Point (Left slot t) = Point (Right slot t) :=
        point_eq_of_glue Pieces ⟨slot, t, rfl, rfl⟩
      exact glued ▸ slot_chart slot t
  obtain ⟨⟨piece, x⟩, rfl⟩ := point_surjective Pieces Banks z
  cases piece with
  | none =>
    by_cases on_cut : Cap.horizontal (restore x).val ∈ R.wholeCarrier
    · change x ∈ {z : L.whole.Cut | Cap.horizontal (restore z).val ∈ R.wholeCarrier} at on_cut
      rw [← L.contourBaseMark_range_eq_cut S] at on_cut
      obtain ⟨a, membership⟩ := Set.mem_iUnion.mp on_cut
      obtain ⟨side, t, rfl⟩ := Set.mem_iUnion.mp membership
      exact addressed ⟨a, none, side, t⟩ trivial
    · exact L.contourGraft_roof_off_cut_regular S x on_cut
  | some e =>
    by_cases inside : x.val ∈ interior (Model[e]).region
    · exact (L.contourGraft_gap_interior_chart S e x inside).modelIsometryEquiv complexPlane
    · obtain ⟨a, member, side, t, rfl⟩ := L.exists_contourGraftGapMark_of_frontier S e x
        ⟨subset_closure x.property, inside⟩
      exact addressed ⟨a, some e, side, t⟩ member

/-- Fibers away from finite interior cut vertices follow from their exact physical addresses. -/
theorem contourGraft_contractibleFiber_of_finite_vertices (f : Graft → Space)
    (on_piece : ∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2)
    (finite_vertex : ∀ e : Child,
      ContractibleSpace {z : Graft | f z = (restore (Base (.inl e) false 0)).val})
    (p : Surface) : ContractibleSpace {z : Graft | f z = p.val} := by
  by_cases on_cut : Cap.horizontal p.val ∈ R.wholeCarrier
  · obtain ⟨x, hx⟩ := L.whole.partition.restoreCut_surjective R.wholeCarrier ⟨p.val, p.property⟩
    have projected := congrArg (fun z : PolygonalPoint Surface => Cap.horizontal z.val) hx
    have same_at (a : Attachment) (t : Param a) (position : Phys a t = Cap.horizontal p.val) :
        (restore (Base a false t)).val = p.val := by
      let E := SpatialEnvelope.wholeSurfaceHomeomorph M.plane
      have eq : E ⟨(restore (Base a false t)).val, (restore (Base a false t)).property⟩ = E p :=
        position
      exact congrArg Subtype.val (E.injective eq)
    have named (a : Attachment) (side : Bool) (t : Param a) (name : Base a side t = x) :
        (restore (Base a false t)).val = p.val := by
      apply same_at
      rw [← L.contourPhysicalAddress_side S a side, name]
      exact projected
    by_cases below : (G).height (Cap.horizontal p.val) < level
    · obtain ⟨e, side, t, name⟩ := L.exists_contourParentMark_of_cut_below S x
        (projected.symm ▸ on_cut) (projected.symm ▸ below)
      have eq := named (.inl e) side t name
      by_cases zero : t = 0
      · subst t
        exact eq ▸ finite_vertex e
      by_cases one : t = 1
      · subst t
        let v := (Fcut).parents.parent e.val
        have h : (Q).projectedVertex v = Cap.horizontal p.val := by
          have h := congrArg Cap.horizontal eq
          change Phys (.inl e) 1 = _ at h
          rwa [L.contourPhysicalAddress_finite S e 1, show (1 : unitInterval).val = 1 from rfl,
            AffineMap.lineMap_apply_one] at h
        have nonroot : v ∉ (Fcut).parents.roots := by
          intro root
          let exit : Exit := ⟨e.val, e.property, root⟩
          have join : Phys (.inr exit) 0 = Phys (.inl e) 1 :=
            congrArg (fun y : L.whole.Cut => Cap.horizontal (restore y).val)
              (L.contourBaseMark_tail_zero S exit false)
          obtain ⟨speed, _, heights⟩ := L.exists_contourPhysicalAddress_tail_height S exit
          have height := heights 0
          have physical : Phys (.inl e) 1 = Cap.horizontal p.val := congrArg Cap.horizontal eq
          rw [join, physical] at height
          change (G).height (Cap.horizontal p.val) = level + speed * 0 at height
          rw [mul_zero, add_zero] at height
          exact below.ne height
        let parent : Child := ⟨v, nonroot⟩
        have location : Phys (.inl parent) 0 = Cap.horizontal p.val := by
          rw [L.contourPhysicalAddress_finite S parent 0, show (0 : unitInterval).val = 0 from rfl,
            AffineMap.lineMap_apply_zero]
          exact h
        exact (same_at (.inl parent) 0 location) ▸ finite_vertex parent
      have strict : 0 < t ∧ t < 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm zero), lt_of_le_of_ne t.property.2 one⟩
      exact eq ▸ L.contourGraftCollapse_fiber_strict S f on_piece (.inl e) t strict
    · obtain ⟨e, side, t, name⟩ := L.exists_contourTailMark_of_cut_above S x
        (projected.symm ▸ on_cut) (projected.symm ▸ le_of_not_gt below)
      have eq := named (.inr e) side t name
      by_cases zero : t = 0
      · subst t
        exact eq ▸ L.contourGraftCollapse_fiber_terminalJoin S f on_piece e
      exact eq ▸ L.contourGraftCollapse_fiber_strict S f on_piece (.inr e) t
        (lt_of_le_of_ne zero_le (Ne.symm zero))
  · exact L.contourGraftCollapse_fiber_off_cut S f on_piece p.property on_cut

local notation "Index" => contourGraftCellIndex L S
local notation "Cells" => contourGraftCells L S
local notation "Raw" => (fun ij : Σ i, Index i => Cells (Sigma.fst ij) (Sigma.snd ij))
local notation "Seams" => contourGraftClosedSeams L S
local notation "RawGraft" => MetricGluing.Realization Raw (MetricGluing.ClosedSeams.relation Seams)

/-- A checked local metric chart at each graft point and contractible collapse fibers
give an isometry of the entire unbounded graft onto the plane. -/
theorem exists_contourGraft_isometry_of_local_charts
    (flat : ∀ z : Graft, HasMetricBallChart Plane z)
    (finite_vertex : ∀ (f : Graft → Space),
      (∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2) →
      ∀ e : Child, ContractibleSpace {z : Graft | f z = (restore (Base (.inl e) false 0)).val}) :
    ∃ develop : Graft → Plane, Isometry develop ∧ Function.Surjective develop := by
  obtain ⟨f, proper, range_eq, on_piece⟩ := L.exists_contourGraftProperCollapse S
  have every (p : Surface) : ContractibleSpace {z : Graft | f z = p.val} :=
    L.contourGraft_contractibleFiber_of_finite_vertices S f on_piece (finite_vertex f on_piece) p
  let E := L.contourGraftClosedSeamsIsometry S
  let spatial (z : Graft) : Surface := ⟨f z, range_eq.le (Set.mem_range_self z)⟩
  have spatial_proper : IsProperMap spatial :=
    isProperMap_of_comp_of_inj (proper.continuous.subtype_mk _)
      continuous_subtype_val proper Subtype.val_injective
  have spatial_onto : Function.Surjective spatial := by
    intro p
    obtain ⟨z, at_p⟩ : p.val ∈ Set.range f := range_eq.symm ▸ p.property
    exact ⟨z, Subtype.ext at_p⟩
  let collapse : RawGraft → Surface := spatial ∘ E
  let : ContractibleSpace Surface := (SpatialEnvelope.wholeSurfaceHomeomorph M.plane).contractibleSpace
  have all_fibers (p : Surface) : ContractibleSpace (collapse ⁻¹' {p}) := by
    let s : Set Graft := {z | f z = p.val}
    have preimage : collapse ⁻¹' {p} = E ⁻¹' s := by
      ext z
      change spatial (E z) = p ↔ f (E z) = p.val
      exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
    rw [preimage]
    let : ContractibleSpace s := every p
    let H := E.toHomeomorph
    exact ((H.image (H ⁻¹' s)).trans (Homeomorph.setCongr (H.image_preimage s))).contractibleSpace
  have cell (ij : Σ i, Index i) := L.contourGraftCell_geometry S ij.1 ij.2
  obtain ⟨develop, preserves, onto⟩ :=
    MetricGluing.exists_global_planar_isometry_of_proper_contractible_fibers Raw
      (Seams).relation collapse
      (spatial_proper.comp E.toHomeomorph.isProperMap) (spatial_onto.comp E.surjective) all_fibers
      (fun ij => (cell ij).1) (fun ij => (cell ij).2.1) (fun ij => (cell ij).2.2)
      (L.contourGraftClosedSeams_boundary S)
      (fun z => (hasMetricBallChart_isometryEquiv_iff E z).mp (flat (E z)))
  exact ⟨develop ∘ E.symm, preserves.comp E.symm.isometry, onto.comp E.symm.surjective⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
