module

public import Unfoldings.FewestNets.ThreeExitGraftAddressCoverage
public import Unfoldings.Roof.AffineFloorCutBoundary

/-! Strict physical addresses of the finite parent edges and their true exit rays. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

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

local instance graftPhysicalAddressIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Base" => contourBaseMark L S
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Root" => {v : V // v ∈ R.stems.choice.parents.roots}
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "vertex" => ConvexRoof.projectedVertex Q
local notation "parent" => AscendingParents.parent (PotentialCutForest.parents Fcut)

/-- The horizontal position of an original cut address is independent of its chosen bank. -/
def contourPhysicalAddress (a : Attachment) (t : Param a) : Plane :=
  Cap.horizontal (restore (Base a false t)).val

local notation "Phys" => contourPhysicalAddress L S

theorem contourPhysicalAddress_finite (e : Child) (t : unitInterval) :
    Phys (.inl e) t = AffineMap.lineMap (vertex e.val) (vertex (parent e.val)) t.val :=
  L.horizontal_contourParentMark S.higher S.contour S.starts e.val e.property false t

theorem contourPhysicalAddress_side (a : Attachment) (side : Bool) (t : Param a) :
    Cap.horizontal (restore (Base a side t)).val = Phys a t := by
  cases side
  · rfl
  · exact congrArg Cap.horizontal (L.restore_contourBaseMark_sides S a t).symm

/-- The strict part of a finite address is inside the affine-floor window. -/
theorem contourPhysicalAddress_finite_lt (e : Child) (t : unitInterval) (strict : 0 < t ∧ t < 1) :
    (G).height (Phys (.inl e) t) < level := by
  rw [L.contourPhysicalAddress_finite S e t]
  exact (G).openSegment_height_lt (contourParentStart_below S e) (contourParentEnd_le S e)
    (lineMap_mem_openSegment ℝ _ _ strict)

theorem contourPhysicalAddress_finite_le (e : Child) (t : unitInterval) :
    (G).height (Phys (.inl e) t) ≤ level := by
  rw [L.contourPhysicalAddress_finite S e t]
  have below : Convex ℝ {q | (G).height q ≤ level} := by
    simpa only [Set.mem_univ, true_and] using (G).convex_height.convex_le level
  exact below.lineMap_mem (contourParentStart_below S e).le (contourParentEnd_le S e) t.property

/-- An interior point of a fine parent bank retains its original edge and parameter. -/
theorem contourPhysicalAddress_finite_unique (e f : Child) (t s : unitInterval)
    (strict : 0 < t ∧ t < 1) (equal : Phys (.inl f) s = Phys (.inl e) t) :
    f = e ∧ s = t := by
  have open_e : Phys (.inl e) t ∈ openSegment ℝ (vertex e.val) (vertex (parent e.val)) := by
    rw [L.contourPhysicalAddress_finite S]
    exact lineMap_mem_openSegment ℝ _ _ strict
  have avoids (v : TriangleComplex.Vertex D Set.univ) : Phys (.inl e) t ≠ vertex v :=
    fun h => (Q).seamEmbedding_straight.openSegment_avoids_vertices ((Selection).link e)
      (h ▸ open_e)
  have line_f := L.contourPhysicalAddress_finite S f s
  have inner_s : 0 < s ∧ s < 1 := by
    refine ⟨lt_of_le_of_ne s.property.1 ?_, lt_of_le_of_ne s.property.2 ?_⟩
    · intro h
      have time := congrArg Subtype.val h
      change (0 : ℝ) = s.val at time
      rw [← time, AffineMap.lineMap_apply_zero] at line_f
      exact avoids f.val (equal.symm.trans line_f)
    · intro h
      have time := congrArg Subtype.val h
      change s.val = (1 : ℝ) at time
      rw [time, AffineMap.lineMap_apply_one] at line_f
      exact avoids (parent f.val) (equal.symm.trans line_f)
  have same : f = e := by
    by_contra different
    have open_f : Phys (.inl e) t ∈ openSegment ℝ (vertex f.val) (vertex (parent f.val)) :=
      (line_f.symm.trans equal) ▸ lineMap_mem_openSegment ℝ _ _ inner_s
    exact Set.disjoint_left.mp ((Q).seamEmbedding_straight.openSegments_disjoint
      (fun eq => different ((Selection).edge_injective eq)) ((Selection).link f)
      ((Selection).link e)) open_f open_e
  subst f
  have ends_ne : vertex e.val ≠ vertex (parent e.val) := by
    intro h
    exact ((Fcut).parents.ascending e.val e.property).ne
      (congrArg (Fcut).parents.height ((Q).projectedVertex_injective h))
  refine ⟨rfl, Subtype.ext (AffineMap.lineMap_injective ℝ ends_ne ?_)⟩
  exact line_f.symm.trans (equal.trans (L.contourPhysicalAddress_finite S e t))

/-- The terminal edge and its continued tail use one actual exit ray, with
the true affine time on the whole roof. -/
theorem exists_contourPhysicalAddress_tail_ray (e : Exit) :
    ∃ (r : Root) (first : ℝ), 0 ≤ first ∧
      let τ := R.exits.timeAtLevel level (R.exitRoot r)
      first < τ ∧
      vertex e.val = R.exits.ray (R.exitRoot r) first ∧
      vertex (parent e.val) = R.exits.pointAtLevel level (R.exitRoot r) ∧
      ∀ t : ℝ≥0, Phys (.inr e) t = R.exits.ray (R.exitRoot r) (τ + (τ - first) * t.val) := by
  obtain ⟨r, first, nonnegative, before, head, tip⟩ :=
    R.exists_exit_of_fineMesh_terminalParent level M S.higher e.val e.property.1 e.property.2
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  let c := L.contourTerminalContinuation S.higher S.contour S.starts e
  let edge : Child := ⟨e.val, e.property.1⟩
  have start : Phys (.inl edge) 0 = R.exits.ray (R.exitRoot r) first := by
    rw [L.contourPhysicalAddress_finite S]
    change AffineMap.lineMap (vertex e.val) (vertex (parent e.val)) (0 : ℝ) = _
    rw [AffineMap.lineMap_apply_zero]
    exact head
  have finish : Phys (.inl edge) 1 = R.exits.ray (R.exitRoot r) τ := by
    rw [L.contourPhysicalAddress_finite S]
    change AffineMap.lineMap (vertex e.val) (vertex (parent e.val)) (1 : ℝ) = _
    rw [AffineMap.lineMap_apply_one]
    exact tip
  refine ⟨r, first, nonnegative, before, head, tip, fun t => ?_⟩
  change Cap.horizontal (restore (c.mark false t)).val = _
  rw [c.position, map_add, map_smul, map_sub]
  change Phys (.inl edge) 1 + t.val • (Phys (.inl edge) 1 - Phys (.inl edge) 0) = _
  rw [start, finish]
  simp only [SlopeEnvelope.ExteriorPlan.ray]
  module

/-- The height of the normalized tail increases with a strictly positive slope. -/
theorem exists_contourPhysicalAddress_tail_height (e : Exit) :
    ∃ speed : ℝ, 0 < speed ∧ ∀ t : ℝ≥0,
      (G).height (Phys (.inr e) t) = level + speed * t.val := by
  obtain ⟨r, first, nonnegative, before, _, _, position⟩ :=
    L.exists_contourPhysicalAddress_tail_ray S e
  let root := R.exitRoot r
  let τ := R.exits.timeAtLevel level root
  have τ_pos := nonnegative.trans_lt before
  have speed_pos := mul_pos (sub_pos.mpr before) (R.exits.positive root)
  refine ⟨(τ - first) * R.exits.rate root, speed_pos, fun t => ?_⟩
  have at_rim : (G).height (R.exits.ray root τ) = level :=
    R.exits.pointAtLevel_height level root (R.exit_origin_below level S.higher r)
  have time_nonneg : 0 ≤ τ + (τ - first) * t.val :=
    add_nonneg τ_pos.le (mul_nonneg (sub_nonneg.mpr before.le) t.property)
  rw [position, R.exits.height_ray root time_nonneg]
  rw [R.exits.height_ray root τ_pos.le] at at_rim
  rw [← at_rim]
  ring

/-- Strict finite bank interiors have a unique address among all the finite
and continued cuts. -/
theorem contourPhysicalAddress_eq_finite (e : Child) (t : unitInterval) (strict : 0 < t ∧ t < 1)
    (a : Attachment) (s : Param a) (equal : Phys a s = Phys (.inl e) t) :
    (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨.inl e, t⟩ := by
  cases a with
  | inl f =>
    obtain ⟨rfl, rfl⟩ := L.contourPhysicalAddress_finite_unique S e f t s strict equal
    rfl
  | inr e' =>
    obtain ⟨speed, sp, position⟩ := L.exists_contourPhysicalAddress_tail_height S e'
    have left := L.contourPhysicalAddress_finite_lt S e t strict
    rw [← equal, position] at left
    exact (not_lt_of_ge (le_add_of_nonneg_right (mul_nonneg sp.le s.property)) left).elim

/-- Points strictly between the ends of a fine terminal segment have strict finite marks. -/
private theorem exists_contourPhysicalAddress_on_terminal_segment (e : Exit) (r : Root)
    {first w : ℝ} (after : first < w) (before : w < R.exits.timeAtLevel level (R.exitRoot r))
    (head : vertex e.val = R.exits.ray (R.exitRoot r) first)
    (tip : vertex (parent e.val) = R.exits.pointAtLevel level (R.exitRoot r)) :
    ∃ u : unitInterval, (0 < u ∧ u < 1) ∧
      Phys (.inl ⟨e.val, e.property.1⟩) u = R.exits.ray (R.exitRoot r) w := by
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have length : 0 < τ - first := sub_pos.mpr (after.trans before)
  let u := (w - first) / (τ - first)
  have lower : 0 < u := div_pos (sub_pos.mpr after) length
  have upper : u < 1 := (div_lt_one length).mpr (sub_lt_sub_right before first)
  let t : unitInterval := ⟨u, lower.le, upper.le⟩
  refine ⟨t, ⟨lower, upper⟩, ?_⟩
  rw [L.contourPhysicalAddress_finite S, head, tip, SlopeEnvelope.ExteriorPlan.pointAtLevel]
  change AffineMap.lineMap (R.exits.ray (R.exitRoot r) first)
    (R.exits.ray (R.exitRoot r) τ) u = _
  have time : first + u * (τ - first) = w := by
    dsimp only [u]
    rw [div_mul_cancel₀ _ length.ne']
    ring
  rw [← time, AffineMap.lineMap_apply_module']
  simp only [SlopeEnvelope.ExteriorPlan.ray]
  module

/-- Every point past the join of a terminal ray has exactly one original address. -/
theorem contourPhysicalAddress_eq_positiveTail (e : Exit) (t : ℝ≥0) (positive : 0 < t)
    (a : Attachment) (s : Param a) (equal : Phys a s = Phys (.inr e) t) :
    (⟨a, s⟩ : Σ a : Attachment, Param a) = ⟨.inr e, t⟩ := by
  obtain ⟨speed, speed_pos, height⟩ := L.exists_contourPhysicalAddress_tail_height S e
  cases a with
  | inl f =>
    have at_f := L.contourPhysicalAddress_finite_le S f s
    rw [equal, height] at at_f
    exact ((lt_add_of_pos_right level (mul_pos speed_pos positive)).not_ge at_f).elim
  | inr f =>
    obtain ⟨r, first, first_nonneg, first_lt, head_e, tip_e, ray_e⟩ :=
      L.exists_contourPhysicalAddress_tail_ray S e
    obtain ⟨r', first', first'_nonneg, first'_lt, head_f, tip_f, ray_f⟩ :=
      L.exists_contourPhysicalAddress_tail_ray S f
    let τ := R.exits.timeAtLevel level (R.exitRoot r)
    let τ' := R.exits.timeAtLevel level (R.exitRoot r')
    have time_e : 0 < τ + (τ - first) * t.val :=
      add_pos_of_pos_of_nonneg (first_nonneg.trans_lt first_lt)
        (mul_nonneg (sub_nonneg.mpr first_lt.le) t.property)
    have time_f : 0 < τ' + (τ' - first') * s.val :=
      add_pos_of_pos_of_nonneg (first'_nonneg.trans_lt first'_lt)
        (mul_nonneg (sub_nonneg.mpr first'_lt.le) s.property)
    have same_root : r' = r := by
      by_contra different
      exact Set.disjoint_left.mp (R.exit_rays_disjoint (R.exitRoot_injective.ne different))
        ⟨_, time_f, ray_f s⟩ ⟨_, time_e, equal.trans (ray_e t)⟩
    subst r'
    let w := (max first first' + τ) / 2
    have last : max first first' < τ := max_lt first_lt first'_lt
    have before : w < τ := by dsimp only [w]; linarith only [last]
    have after : max first first' < w := by dsimp only [w]; linarith only [last]
    obtain ⟨u, u_strict, mark_e⟩ := L.exists_contourPhysicalAddress_on_terminal_segment S e r
      ((le_max_left _ _).trans_lt after) before head_e tip_e
    obtain ⟨v, _, mark_f⟩ := L.exists_contourPhysicalAddress_on_terminal_segment S f r
      ((le_max_right _ _).trans_lt after) before head_f tip_f
    obtain ⟨edge_eq, _⟩ := L.contourPhysicalAddress_finite_unique S
      ⟨e.val, e.property.1⟩ ⟨f.val, f.property.1⟩ u v u_strict
      (mark_f.trans mark_e.symm)
    have same_vertex : f.val = e.val := congrArg (fun v : Child => v.val) edge_eq
    have same : f = e := Subtype.ext same_vertex
    subst f
    have h := congrArg (G).height equal
    rw [height s, height t] at h
    have parameters : s = t := NNReal.eq (mul_left_cancel₀ speed_pos.ne' (add_left_cancel h))
    subst s
    rfl

/-- At a vertex below the level, all physical marks are either ends of incoming
fine edges or the start of the outgoing fine edge. -/
theorem contourPhysicalAddress_at_vertex
    (v : TriangleComplex.Vertex D Set.univ) (below : (G).height (vertex v) < level)
    (a : Attachment) (s : Param a) (equal : Phys a s = vertex v) :
    ∃ e : Child, ((⟨a, s⟩ : Σ b : Attachment, Param b) = ⟨.inl e, 0⟩ ∧ e.val = v) ∨
      ((⟨a, s⟩ : Σ b : Attachment, Param b) = ⟨.inl e, 1⟩ ∧ parent e.val = v) := by
  cases a with
  | inr r =>
    obtain ⟨rate, positive, heights⟩ := L.exists_contourPhysicalAddress_tail_height S r
    have above : level ≤ (G).height (Phys (.inr r) s) := by
      rw [heights]
      exact le_add_of_nonneg_right (mul_nonneg positive.le s.property)
    rw [equal] at above
    exact (not_lt_of_ge above below).elim
  | inl e =>
    have at_edge := L.contourPhysicalAddress_finite S e s
    by_cases h₀ : s.val = 0
    · have endpoint := (congrArg (AffineMap.lineMap (vertex e.val)
        (vertex (parent e.val))) h₀).trans (AffineMap.lineMap_apply_zero ..)
      have same := (Q).projectedVertex_injective (endpoint.symm.trans (at_edge.symm.trans equal))
      exact ⟨e, Or.inl ⟨congrArg (fun u : unitInterval => (⟨.inl e, u⟩ : Σ b, Param b))
        (Subtype.ext h₀), same⟩⟩
    by_cases h₁ : s.val = 1
    · have endpoint := (congrArg (AffineMap.lineMap (vertex e.val)
        (vertex (parent e.val))) h₁).trans (AffineMap.lineMap_apply_one ..)
      have same := (Q).projectedVertex_injective (endpoint.symm.trans (at_edge.symm.trans equal))
      exact ⟨e, Or.inr ⟨congrArg (fun u : unitInterval => (⟨.inl e, u⟩ : Σ b, Param b))
        (Subtype.ext h₁), same⟩⟩
    have impossible : vertex v ∈ openSegment ℝ (vertex e.val)
        (vertex (parent e.val)) := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨s.val, ⟨lt_of_le_of_ne s.property.1 (Ne.symm h₀), lt_of_le_of_ne s.property.2 h₁⟩,
        at_edge.symm.trans equal⟩
    exact ((Q).seamEmbedding_straight.openSegment_avoids_vertices ((Selection).link e) impossible).elim

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
