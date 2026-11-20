module

public import Unfoldings.Roof.CompatibleContourTerminalSideLabels
public import Unfoldings.Roof.CompatibleCompletionRootwardFans
public import Unfoldings.Roof.OriginalCutLabels

/-! Each original terminal continuation has a last fine edge and two named tail banks. -/

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

local instance sourceOnlyTailAddressCoverageIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyTailAddressCoverageWholeFintype : Fintype W.Index := W.finiteIndex

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

set_option maxHeartbeats 2200000 in
-- Membership in the finite union retains the dependent original fine edge.
/-- Every original terminal ray has an actual last finite parent edge at the truncation level. -/
theorem exists_compatibleContourTerminalEdge_at_root (r : {v // v ∈ R.parents.roots}) :
    ∃ e : Terminal, RootAt[e] = r := by
  classical
  let head (e : Edge) := (Q).projectedVertex e.val
  let tip (e : Edge) := (Q).projectedVertex ((Fcut).parents.parent e.val)
  let covered := ⋃ e : Edge, segment ℝ (head e) (tip e)
  have closed : IsClosed covered := by
    apply isClosed_iUnion_of_finite
    intro e
    rw [segment_eq_image_lineMap]
    have continuous_line : Continuous (fun t : ℝ => AffineMap.lineMap (head e) (tip e) t) := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    exact (isCompact_Icc.image continuous_line).isClosed
  let ray (t : ℝ) := R.exterior.ray (R.terminalIndex r) t
  let τ := R.terminalTime level r
  have τpos : 0 < τ := R.terminalTime_pos level higher r
  have ray_continuous : Continuous ray := by
    unfold ray SlopeEnvelope.ExteriorPlan.ray
    fun_prop
  have approach : Set.Ioo 0 τ ⊆ ray ⁻¹' covered := by
    intro t ht
    have below := (R.terminal_ray_below_iff level higher r ht.1.le).mpr ht.2
    have on_cut : ray t ∈ R.truncatedCarrier level higher :=
      (R.mem_truncatedCarrier_iff level higher below.le).mpr
        (Or.inr (Set.mem_iUnion.mpr ⟨r, t, ht.1.le, rfl⟩))
    have inside : ray t ∈ interior (SpatialEnvelope.clip M.plane (-level)) := by
      rw [M.clip_eq_sublevel, neg_neg]
      exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
    obtain ⟨s, unretained, on_edge⟩ := K.compatibleCutMesh_cut_seam compact nonempty R no_boundary
      level higher M positive inner_disk on_cut inside
    have removed : s ∉ (Fcut).retain := by
      rwa [K.compatibleMesh_retain_eq_prescribed compact nonempty R no_boundary level higher
        M positive inner_disk beta acute]
    obtain ⟨e, named⟩ : s ∈ Set.range (Selection).edge := Classical.not_not.mp removed
    have names := (Q).projected_link_segment ((Selection).link e)
    rw [named] at names
    rw [← (T).toTriangulation.roof_projectedTriangle Conforming Inside] at on_edge
    exact Set.mem_iUnion.mpr ⟨e, names.symm ▸ on_edge⟩
  have approaching : τ ∈ closure (Set.Ioo 0 τ) := by
    rw [closure_Ioo (Ne.symm τpos.ne')]
    exact ⟨τpos.le, le_rfl⟩
  have on_terminal : R.terminalPoint level r ∈ covered :=
    closure_minimal approach (closed.preimage ray_continuous) approaching
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp on_terminal
  have low : Height (head e) < level := K.compatibleMesh_nonroot_height_lt compact nonempty R
    no_boundary level higher M positive inner_disk beta acute e.val e.property
  have high : Height (tip e) ≤ level := by
    have h := (Q).projectedVertex_mem_footprint ((Fcut).parents.parent e.val)
    rw [(T).toTriangulation.roof_footprint Conforming Inside, M.clip_eq_sublevel, neg_neg] at h
    exact h
  obtain ⟨t, bound, point⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_edge
  have at_level := R.terminalPoint_level level higher r
  have at_end : t = 1 := by
    by_contra not_end
    have below : Height (R.terminalPoint level r) < level := by
      by_cases start : t = 0
      · rw [start, AffineMap.lineMap_apply_zero] at point
        exact point ▸ low
      · apply (K.clippedExtension slopes compact nonempty).openSegment_height_lt low high
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨lt_of_le_of_ne bound.1 (Ne.symm start), lt_of_le_of_ne bound.2 not_end⟩, point⟩
    exact below.ne at_level
  rw [at_end, AffineMap.lineMap_apply_one] at point
  have root : (Fcut).parents.parent e.val ∈ (Fcut).parents.roots := by
    by_contra hn
    have lt := K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level
      higher M positive inner_disk beta acute ((Fcut).parents.parent e.val) hn
    change Height (tip e) < level at lt
    exact lt.ne ((congrArg Height point).trans at_level)
  let terminal : Terminal := ⟨e.val, e.property, root⟩
  have at_root : (Fcut).parents.root terminal.val = (Fcut).parents.parent terminal.val :=
    ((Fcut).parents.root_eq_of_ancestor ((Fcut).parents.ancestor_parent terminal.val)).trans
      ((Fcut).parents.root_of_root root)
  have this := K.compatibleMeshTerminalRoot_point compact nonempty R no_boundary level higher M
    positive inner_disk beta acute terminal.val ((D).contourTerminalEdge_positive Selection terminal)
  rw [at_root] at this
  have equal : R.terminalPoint level RootAt[terminal] = R.terminalPoint level r := this.symm.trans point
  have same : RootAt[terminal] = r := by
    apply Sum.inr.inj
    exact K.truncatedPoint_injective compact nonempty R no_boundary level higher
      (show R.truncatedPoint level (.inr RootAt[terminal]) =
        R.truncatedPoint level (.inr r) from equal)
  exact ⟨terminal, same⟩

set_option maxHeartbeats 2200000 in
-- The two independently recovered original whole-bank labels must be compared at their rim values.
/-- At and beyond the truncation level, every roof copy of a physical cut point
is a mark on a genuine infinite bank at its original parameter. -/
theorem compatibleContourTailMark_exists_of_mem_cut_above
    (x : W.Cut) (on_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∈ R.carrier)
    (above : level ≤ Height (Cap.horizontal (W.partition.restoreCut R.carrier x).val)) :
    ∃ (e : Terminal) (side : Bool) (t : ℝ≥0), TailAt[e,side,t] = x := by
  let p := Cap.horizontal (W.partition.restoreCut R.carrier x).val
  rcases on_cut with finite | terminal
  · obtain ⟨e, on_segment⟩ := Set.mem_iUnion.mp finite
    obtain ⟨t, bounds, ht⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_segment
    have less : Height p < level := by
      by_cases start : t = 0
      · rw [start, AffineMap.lineMap_apply_zero] at ht
        have at_p : _ = p := ht
        exact (congrArg Height at_p).symm.trans_lt (higher _)
      by_cases finish : t = 1
      · rw [finish, AffineMap.lineMap_apply_one] at ht
        have at_p : _ = p := ht
        exact (congrArg Height at_p).symm.trans_lt (higher _)
      · apply (K.clippedExtension slopes compact nonempty).openSegment_height_lt
          (higher e.val) (higher (R.parents.parent e.val)).le
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨lt_of_le_of_ne bounds.1 (Ne.symm start), lt_of_le_of_ne bounds.2 finish⟩, ht⟩
    exact (not_lt_of_ge above less).elim
  · obtain ⟨r, s, s_nonnegative, loc⟩ := Set.mem_iUnion.mp terminal
    change p = R.exterior.ray (R.terminalIndex r) s at loc
    obtain ⟨e, root⟩ := K.exists_compatibleContourTerminalEdge_at_root compact nonempty R
      no_boundary level higher M positive inner_disk beta acute r
    subst r
    let r := RootAt[e]
    let τ := R.terminalTime level r
    have τpos : 0 < τ := R.terminalTime_pos level higher r
    have before : τ ≤ s := (R.terminal_ray_superlevel_iff level higher r s_nonnegative).mp
      ((congrArg Height loc) ▸ above)
    have s_pos : 0 < s := τpos.trans_le before
    let speed := SpeedAt[e]
    have speed_pos : 0 < speed.val := K.compatibleContourTerminalSpeed_positive compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e
    let time : ℝ≥0 := ⟨s, s_nonnegative⟩
    let start : ℝ≥0 := ⟨τ, τpos.le⟩
    let t : ℝ≥0 := ⟨(s - τ) / speed.val, div_nonneg (sub_nonneg.mpr before) speed_pos.le⟩
    have normalized : forwardBankParameter start speed t = time := by
      apply NNReal.eq
      change τ + speed.val * ((s - τ) / speed.val) = s
      rw [mul_comm speed.val, div_mul_cancel₀ _ speed_pos.ne']
      ring
    obtain ⟨label, target, _⟩ := K.existsUnique_wholeTerminalBank_side compact nonempty R
      no_boundary W r time s_pos x loc
    obtain ⟨left, first⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e false
    obtain ⟨right, last⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W e true
    have opposite : left ≠ right := by
      intro same
      have equal : TailAt[e,false,0] = TailAt[e,true,0] :=
        (first 0).trans (same ▸ (last 0).symm)
      rw [K.compatibleContourTerminalMark_zero, K.compatibleContourTerminalMark_zero] at equal
      exact K.compatibleContourTerminalEndpoint_ne compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W e equal
    by_cases h : label = left
    · have marked := first t
      change TailAt[e,false,t] = K.wholeTerminalBank compact nonempty R no_boundary W r left
        (forwardBankParameter start speed t) at marked
      rw [normalized, ← h] at marked
      exact ⟨e, false, t, marked.trans target.symm⟩
    · have opposite_labels (x y z : Bool) (xy : x ≠ y) (zy : z ≠ y) : x = z := by
        cases y
        · have hx : x = true := by cases x; exact (xy rfl).elim; rfl
          have hz : z = true := by cases z; exact (zy rfl).elim; rfl
          exact hx.trans hz.symm
        · have hx : x = false := by cases x; rfl; exact (xy rfl).elim
          have hz : z = false := by cases z; rfl; exact (zy rfl).elim
          exact hx.trans hz.symm
      have chosen : label = right := opposite_labels label left right h (Ne.symm opposite)
      have marked := last t
      change TailAt[e,true,t] = K.wholeTerminalBank compact nonempty R no_boundary W r right
        (forwardBankParameter start speed t) at marked
      rw [normalized, ← chosen] at marked
      exact ⟨e, true, t, marked.trans target.symm⟩

end Unfoldings.ConvexRoof
