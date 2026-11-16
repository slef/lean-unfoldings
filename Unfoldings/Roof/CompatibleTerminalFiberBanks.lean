module

public import Unfoldings.Roof.CompatibleWholeBankCellAgreement
public import Unfoldings.Geometry.SpatialEnvelopeIncidentSupport

/-! Every original positive terminal-ray metric copy is one of the constructed whole banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel.TerminalSupportCells

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  {W : R.WholeCutModel M} {r : {v // v ∈ R.parents.roots}} (B : W.TerminalSupportCells r)

local instance terminalFiberBankIndexFintype : Fintype W.Index := W.finiteIndex

/-- Every original cell at a positive terminal point uses that side's actual whole-ray support. -/
theorem incident_support_eq (a : W.Index) {t : ℝ} (positive : 0 < t)
    (member : R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint a) :
    (M.plane (W.partition.support a)).height =
      (M.plane (W.partition.support (B.anchor (W.terminalSigns r a)))).height := by
  let side := W.terminalSigns r a
  let anchor := B.anchor side
  obtain ⟨δ, δpos, germ⟩ := R.exterior.terminal_cell_ray_germ M W.partition
    (R.terminalIndex r) anchor B.threshold (B.tail side) (W.terminalSigns r anchor)
    ((aligned_exterior (W := W)) anchor) positive
  apply W.partition.incident_support_eq_of_side_germ anchor a
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (W.terminalSigns r) (aligned_exterior (W := W)) member (B.sides side).symm
    Metric.isOpen_ball (Metric.mem_ball_self δpos)
  exact fun z near on_side => germ z near on_side

/-- Each one-ray-cut copy at a positive time is exactly one of the two original whole banks. -/
theorem exists_oneRayBank (t : ℝ≥0) (positive : 0 < t.val)
    (x : W.partition.Cut (R.terminalRayCut r))
    (position : Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) x).val =
      R.exterior.ray (R.terminalIndex r) t.val) : ∃ side, x = B.oneRayBank side t := by
  obtain ⟨⟨a, q⟩, rfl⟩ := MetricGluing.point_surjective (fun a => W.partition.planarCell a)
    (W.partition.cutGlue (R.terminalRayCut r)) x
  let side := W.terminalSigns r a
  let anchor := B.anchor side
  let y := W.partition.cellIsometryEquiv a q
  let source := R.exterior.faceSideRaySource M W.partition (R.terminalIndex r) anchor
    (W.terminalSigns r) B.threshold (B.tail side) t
  have member : R.exterior.ray (R.terminalIndex r) t.val ∈ W.partition.footprint a :=
    Eq.mp (congrArg (fun p : Plane => p ∈ W.partition.footprint a) position)
      (W.partition.horizontal_mem_footprint a q)
  let index : W.partition.FaceSideIndex anchor (W.terminalSigns r) :=
    ⟨a, B.incident_support_eq a positive member, (B.sides side).symm⟩
  have graph : y.val =
      SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) := by
    obtain ⟨p, hp, equal⟩ := q.property
    have horizontal : p = R.exterior.ray (R.terminalIndex r) t.val := by
      change Cap.horizontal ((M.plane (W.partition.support a)).place q.val) = _ at position
      rw [(M.plane (W.partition.support a)).horizontal_place, ← equal,
        (M.plane (W.partition.support a)).project.apply_symm_apply] at position
      exact position
    change (M.plane (W.partition.support a)).place q.val = _
    rw [← equal]
    exact (SpatialEnvelope.point_eq_place M.plane (W.partition.support a)
      (W.partition.active a p hp)).symm.trans (congrArg (SpatialEnvelope.point M.plane) horizontal)
  have placed : y.val = (M.plane (W.partition.support anchor)).place source.val :=
    graph.trans (SpatialEnvelope.point_eq_place M.plane (W.partition.support anchor)
      (R.exterior.terminal_cell_support_active M W.partition (R.terminalIndex r) anchor
        B.threshold (B.tail side) t.val t.property))
  refine ⟨side, ?_⟩
  apply (W.partition.cutIsometryEquiv (R.terminalRayCut r)).injective
  exact (W.partition.faceSideRegionMap_eq_of_spatial_copy anchor
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r))
    index y source placed).symm

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel.TerminalSupportCells

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance fullTerminalFiberBankIndexFintype : Fintype W.Index := W.finiteIndex

include no_boundary in
/-- The actual whole forest cut has exactly its two named whole-bank copies above every
positive terminal-ray point. This also identifies finite comparison copies there. -/
theorem existsUnique_wholeTerminalBank_side (r : {v // v ∈ R.parents.roots})
    (t : ℝ≥0) (positive : 0 < t.val) (x : W.Cut)
    (position : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
      R.exterior.ray (R.terminalIndex r) t.val) :
    ∃! side : Bool, x = K.wholeTerminalBank compact nonempty R no_boundary W r side t := by
  let B := W.terminalSupportCells r
  let forget := W.partition.forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r)
  have restored : Cap.horizontal
      (W.partition.restoreCut (R.terminalRayCut r) (forget x)).val =
        R.exterior.ray (R.terminalIndex r) t.val :=
    (congrArg (fun p => Cap.horizontal p.val) (W.partition.restoreCut_forgetCut R.carrier
      (R.terminalRayCut r) (R.terminalRayCut_subset_carrier r) x)).trans position
  obtain ⟨side, image⟩ := B.exists_oneRayBank t positive (forget x) restored
  have bank_image : forget (K.wholeTerminalBank compact nonempty R no_boundary W r side t) =
      B.oneRayBank side t :=
    K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r
      (B.oneRayBankDilation side) (B.horizontal_restoreCut_oneRayBank side)
      (Dilation.lipschitzWith (B.oneRayBankDilation side)) t
  have unique := (K.existsUnique_terminalRayCut_preimage compact nonempty R no_boundary W r
    positive (B.oneRayBank side t) (B.horizontal_restoreCut_oneRayBank side t)).choose_spec
  have same : x = K.wholeTerminalBank compact nonempty R no_boundary W r side t :=
    (unique.2 x image).trans (unique.2 _ bank_image).symm
  refine ⟨side, same, ?_⟩
  intro other equal
  by_contra different
  exact (K.wholeTerminalBank_ne compact nonempty R no_boundary W r other side different
    t t positive) (equal.symm.trans same)

/-- Membership in a named whole bank identifies the exact original copy at its actual parameter. -/
theorem wholeTerminalBank_eq_of_mem_range (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) (positive : 0 < t.val) (x : W.Cut)
    (position : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    (member : x ∈ Set.range (K.wholeTerminalBank compact nonempty R no_boundary W r side)) :
    x = K.wholeTerminalBank compact nonempty R no_boundary W r side t := by
  obtain ⟨other, equal, _⟩ :=
    K.existsUnique_wholeTerminalBank_side compact nonempty R no_boundary W r t positive x position
  obtain ⟨s, at_bank⟩ := member
  by_cases same : other = side
  · exact same ▸ equal
  · exact False.elim ((K.wholeTerminalBank_ne compact nonempty R no_boundary W r other side
      same t s positive) (equal.symm.trans at_bank.symm))

/-- A continuous connected curve of positive terminal-ray copies follows one fixed whole bank.
The original bank label cannot switch at finite mesh vertices or subdivision points. -/
theorem wholeTerminalBank_side_constant {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (r : {v // v ∈ R.parents.roots}) (curve : A → W.Cut) (continuous : Continuous curve)
    (time : A → ℝ≥0) (positive : ∀ a, 0 < (time a).val)
    (position : ∀ a, Cap.horizontal (W.partition.restoreCut R.carrier (curve a)).val =
      R.exterior.ray (R.terminalIndex r) (time a).val) :
    ∃ side : Bool, ∀ a,
      curve a = K.wholeTerminalBank compact nonempty R no_boundary W r side (time a) := by
  let S (side : Bool) : Set A := curve ⁻¹'
    Set.range (K.wholeTerminalBank compact nonempty R no_boundary W r side)
  have closed (side : Bool) : IsClosed (S side) :=
    (K.wholeTerminalBank_isClosedEmbedding compact nonempty R no_boundary W r side
      ).isClosed_range.preimage continuous
  have cover : Set.univ ⊆ S false ∪ S true := by
    intro a _
    obtain ⟨side, equal, _⟩ := K.existsUnique_wholeTerminalBank_side compact nonempty R
      no_boundary W r (time a) (positive a) (curve a) (position a)
    cases side
    · exact Or.inl ⟨time a, equal.symm⟩
    · exact Or.inr ⟨time a, equal.symm⟩
  have disjoint : Disjoint (S false) (S true) := by
    apply Set.disjoint_left.mpr
    intro a left right
    obtain ⟨s, first⟩ := left
    obtain ⟨t, last⟩ := right
    obtain ⟨side, equal, _⟩ := K.existsUnique_wholeTerminalBank_side compact nonempty R
      no_boundary W r (time a) (positive a) (curve a) (position a)
    cases side
    · exact (K.wholeTerminalBank_ne compact nonempty R no_boundary W r false true
        (by decide) (time a) t (positive a)) (equal.symm.trans last.symm)
    · exact (K.wholeTerminalBank_ne compact nonempty R no_boundary W r true false
        (by decide) (time a) s (positive a)) (equal.symm.trans first.symm)
  have fixed : ∃ side, ∀ a, a ∈ S side := by
    by_cases left : (S false).Nonempty
    · refine ⟨false, fun a => ?_⟩
      rcases cover (Set.mem_univ a) with member | member
      · exact member
      · obtain ⟨b, hb⟩ := left
        obtain ⟨c, _, first, last⟩ := isPreconnected_closed_iff.mp isPreconnected_univ
          (S false) (S true) (closed false) (closed true) cover
          ⟨b, Set.mem_univ b, hb⟩ ⟨a, Set.mem_univ a, member⟩
        exact False.elim (Set.disjoint_left.mp disjoint first last)
    · refine ⟨true, fun a => ?_⟩
      rcases cover (Set.mem_univ a) with member | member
      · exact False.elim (left ⟨a, member⟩)
      · exact member
  obtain ⟨side, all⟩ := fixed
  exact ⟨side, fun a => K.wholeTerminalBank_eq_of_mem_range compact nonempty R no_boundary W r
    side (time a) (positive a) (curve a) (position a) (all a)⟩

end Unfoldings.ConvexRoof
