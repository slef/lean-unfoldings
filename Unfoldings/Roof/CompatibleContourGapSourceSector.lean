module

public import Unfoldings.Roof.CompatibleContourGapModels
public import Unfoldings.Geometry.OpeningSourceAngle
public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.SourceSectorCoordinates
public import Unfoldings.Geometry.TwoBankGapSourceChart

/-! The actual canonical gap begins with the original fresh-source angular defect. -/

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

local instance contourGapSourceSectorMeshFintype : Fintype (T).Index :=
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

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "SpanAt[" e "]" => TriangleComplex.positiveContourBank_span D Selection contour e
local notation "LengthAt[" e "]" =>
  TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts e
local notation "OpenedAt[" e "]" => K.compatibleContourOpenedBank compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts e


local notation "P" => PotentialCutForest.parents Fcut
local notation "VertexAt[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "Defect[" e "]" => TriangleComplex.interiorAngularDefect D Set.univ VertexAt[e]

omit beta acute in
private theorem castOpenings_heading {n m : ℕ} (h : n = m)
    (events : List (Opening n)) (i : Fin m) :
    openingHeading (castOpenings h events) i = openingHeading events (Fin.cast h.symm i) := by
  subst m
  have same : castOpenings rfl events = events := List.map_id' events
  rw [same]
  rfl

/-- The actual first opened edge rotates the original first edge by precisely the source defect.
The preceding history gives no opening on the first edge of this fresh source. -/
theorem compatibleContourOpenedBank_first_edge (event : Event) :
    (OpenedAt[event]).chain.edge 0 =
      complexRotation Defect[event] ((BankAt[event]).chain.edge 0) := by
  let v := VertexAt[event]
  let stage := event.val
  let n := LengthAt[event]
  let span := SpanAt[event]
  let old := (D).contourRootwardOpenings Selection contour stage.castSucc v
  let F := (D).contourFrontier Selection contour stage.castSucc
  let w := (D).interiorAngularDefect Set.univ
  have fresh : v ∉ F.processed := event.property.1
  have none : F.processedDescendants v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x member
    obtain ⟨hx, reaches⟩ := (F.mem_processedDescendants v x).mp member
    obtain ⟨k, equal⟩ := reaches
    exact fresh (equal ▸ F.iterate_mem_of_mem hx k)
  have weight_zero : F.processedDescendantWeight w v = 0 := by
    rw [AscendingParents.ParentFrontier.processedDescendantWeight, none, Finset.sum_empty]
  let i := Fin.cast span.symm (0 : Fin (n + 1))
  have at_source : i.castSucc = 0 := Fin.ext rfl
  have old_zero : openingHeading old i = 0 := by
    let seeds := ((D).selectedContourSeeds Selection contour).take stage.castSucc.val
    change openingHeading ((P).historyOpenings seeds ⟨(P).root v, (P).root_mem v⟩
      ((P).rootwardVertexPath v) ((P).rootwardVertexPath_last v) w) i = 0
    rw [(P).historyOpenings_heading _ _ _ _ _ ((P).rootwardVertexPath_ancestor v),
      at_source, (P).rootwardVertexPath_zero]
    exact weight_zero
  have cast_zero : openingHeading (castOpenings span old) 0 = 0 :=
    (castOpenings_heading span old 0).trans old_zero
  let bank := BankAt[event]
  have update := (D).contourRootwardOpenings_source_bank_of_boundary_roots Selection
    (Fcut).boundary_roots contour starts stage fresh (bank.cast span.symm)
  have same := congrArg (fun Q : PolygonalRay ℂ ((P).distanceToRoot v) => Q.cast span)
    update
  let κ := Defect[event]
  change ((bank.cast span.symm).openings ((D).contourRootwardOpenings Selection contour
    stage.succ v)).cast span = ((bank.cast span.symm).openings (⟨0, κ⟩ :: old)).cast span at same
  simp only [PolygonalRay.cast_openings, PolygonalRay.cast_cast, castOpenings_cons,
    Opening.cast_source] at same
  change (bank.openings (castOpenings span
    ((D).contourRootwardOpenings Selection contour stage.succ v))).chain.edge 0 = _
  rw [same, PolygonalRay.openings_chain, PolygonalChain.openings_edge, complexRotation_apply]
  have heading : openingHeading (⟨0, Defect[event]⟩ :: castOpenings span old) 0 =
      Defect[event] := by
    change Defect[event] + openingHeading (castOpenings span old) 0 = _
    rw [cast_zero, add_zero]
  rw [heading]

omit beta acute in
/-- The complete original first-edge trace is the initial straight segment of a real bank. -/
private theorem initial_edge_segment {n : ℕ} (B : PolygonalRay ℂ (n + 1)) :
    segment ℝ B.start (B.start + B.chain.edge 0) ⊆ B.carrier := by
  have finish : B.start + B.chain.edge 0 = B.chain.vertex (0 : Fin (n + 1)).succ := by
    change B.chain.vertex 0 +
      (B.chain.vertex (0 : Fin (n + 1)).succ - B.chain.vertex 0) = _
    abel
  rw [finish, segment_eq_image_lineMap]
  rintro _ ⟨s, bounds, rfl⟩
  exact Or.inl (B.chain.point_mem_path_range 0 (⟨s, bounds⟩ : unitInterval))

/-- The physical source has its unreduced original defect and it is below a half-turn. -/
theorem compatibleContourGap_source_angle_and_lt_pi
    (event : Event) (G : OrientedBankGap (BankAt[event]) (OpenedAt[event])) :
    initialGapAngle ((BankAt[event]).chain.edge 0) ((OpenedAt[event]).chain.edge 0) =
      Defect[event] ∧ Defect[event] < Real.pi := by
  let κ := Defect[event]
  let first := BankAt[event]
  let second := OpenedAt[event]
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  have rotation : e = complexRotation κ d :=
    K.compatibleContourOpenedBank_first_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event
  have hd : d ≠ 0 :=
    (D).boundaryChainRoll_edge_ne_zero
      (K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts event.val event.property.1 LengthAt[event]
        SpanAt[event]) 0
  have he : e ≠ 0 := rotation.symm ▸ by
    rw [complexRotation_apply]
    exact mul_ne_zero (polarRay_ne_zero _) hd
  have initial := first.initialGapAngle_bounds second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase d e hd he (initial_edge_segment first)
    (initial_edge_segment second)
  have κpos : 0 < κ := event.property.2
  have below : κ < 2 * Real.pi := by
    have internal : ¬ (D).IsBoundaryVertex Set.univ VertexAt[event] := by
      intro at_boundary
      have empty : κ = 0 := by
        change (D).interiorAngularDefect Set.univ VertexAt[event] = 0
        rw [TriangleComplex.interiorAngularDefect, ite_eq_left at_boundary]
      exact κpos.ne' empty
    have defect : κ = 2 * Real.pi - (D).totalAngle Set.univ VertexAt[event] := by
      change (D).interiorAngularDefect Set.univ VertexAt[event] = _
      rw [TriangleComplex.interiorAngularDefect, ite_eq_right internal]
    rw [defect]
    exact sub_lt_self _ ((D).totalAngle_pos Set.univ VertexAt[event])
  have ray : polarRay (initialGapAngle d e) = polarRay κ := by
    rw [polarRay_initialGapAngle d e hd he, rotation, (complexRotation κ).norm_map,
      complexRotation_apply]
    have nonzero : (‖d‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd)
    field_simp
  have same := congrArg Complex.im ray
  simp only [polarRay_im] at same
  have sin_pos : 0 < Real.sin κ :=
    (Real.sin_pos_of_pos_of_lt_pi initial.1 initial.2).trans_eq same
  have acute_defect : κ < Real.pi := by
    by_contra h
    have nonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (show κ - 2 * Real.pi ≤ 0 by linarith)
      (show -Real.pi ≤ κ - 2 * Real.pi by linarith [le_of_not_gt h])
    rw [Real.sin_sub_two_pi] at nonpos
    exact (not_lt_of_ge nonpos) sin_pos
  refine ⟨?_, acute_defect⟩
  change initialGapAngle d e = κ
  rw [rotation]
  exact initialGapAngle_rotated d hd κpos acute_defect

/-- The actual source gap sector has the original angular defect, including its
unreduced value, and keeps the original initial edge frame. -/
theorem compatibleContourGap_source_angle
    (event : Event) (G : OrientedBankGap (BankAt[event]) (OpenedAt[event])) :
    initialGapAngle ((BankAt[event]).chain.edge 0) ((OpenedAt[event]).chain.edge 0) =
      Defect[event] := by
  exact (K.compatibleContourGap_source_angle_and_lt_pi compact nonempty R no_boundary level higher
    M positive inner_disk beta acute contour starts event G).1

/-- The canonical gap's actual source has a whole sector ball of exactly the original
source defect angle, with its original first edge as the initial axis. -/
theorem compatibleContourGap_source_sector_chart
    (event : Event) (G : OrientedBankGap (BankAt[event]) (OpenedAt[event])) :
    let first := BankAt[event]
    let d := first.chain.edge 0
    let e := (OpenedAt[event]).chain.edge 0
    let r := min ‖d‖ ‖e‖
    0 < r ∧ initialGapAngle d e = Defect[event] ∧
      ∃ A : Metric.eball (G.model.edgePoint false 0 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.ball (initialGapSectorOrigin d e) r,
        ∀ y, first.start + (d / (‖d‖ : ℂ)) * (A y).val.val = y.val.val := by
  let first := BankAt[event]
  let second := OpenedAt[event]
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  let r := min ‖d‖ ‖e‖
  have hd : d ≠ 0 :=
    (D).boundaryChainRoll_edge_ne_zero
      (K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts event.val event.property.1 LengthAt[event]
        SpanAt[event]) 0
  have rotation : e = complexRotation Defect[event] d :=
    K.compatibleContourOpenedBank_first_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event
  have he : e ≠ 0 := rotation.symm ▸ by
    rw [complexRotation_apply]
    exact mul_ne_zero (polarRay_ne_zero _) hd
  let source := first.twoBankSourcePoint second G.first_outward G.first_nonzero G.second_outward
    G.second_nonzero G.phase
  have named : (G.model.edgePoint false 0 0) = source := by
    apply PolygonalPoint.ext
    change first.chain.point 0 0 = first.start
    rw [PolygonalChain.point_zero]
    rfl
  refine ⟨lt_min (norm_pos_iff.mpr hd) (norm_pos_iff.mpr he),
    K.compatibleContourGap_source_angle compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts event G, ?_⟩
  rw [named]
  obtain ⟨A, physical⟩ := first.exists_twoBankGap_source_sector_isometry second G.first_outward
    G.first_nonzero G.second_outward G.second_nonzero G.phase d e hd he
      (initial_edge_segment first) (initial_edge_segment second)
  let B := initialGapSectorBallIsometry first.start d e hd r
  refine ⟨A.trans B.symm, fun y => ?_⟩
  have coords : B (B.symm (A y)) = A y := B.apply_symm_apply (A y)
  exact (congrArg (fun z => z.val.val) coords).trans (physical y)

end Unfoldings.ConvexRoof
