module

public import Unfoldings.Cap.ExtendedWaterfallRegular
public import Unfoldings.Cap.CenteredBankTrace
public import Unfoldings.Cap.CenteredBankTraceRadial
public import Unfoldings.Cap.CompletedLinearError
public import Unfoldings.Cap.ClosedSectorStrip
public import Unfoldings.Cap.DevelopedDirectionNorm
public import Unfoldings.Cap.MatchedBankTrace
public import Unfoldings.Cap.RegularWaterfallBankWidth
public import Unfoldings.Geometry.NearIdentityMargins

public import Unfoldings.Cap.RadialBankTraceProperty
public import Unfoldings.Cap.CenteredClosedBankTrace
public import Unfoldings.Cap.RadialStripTraceData

/-! Retain source normalization, coherent pinches, visibility, and radial trace bounds uniformly. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap

universe u v

/-- The actual bank-order calibration has strictly radial complete strip-bank traces.
Only cap geometry and the constructed forest are inputs; the threshold precedes both meshes. -/
theorem exists_uniform_extended_radial_strip_data (t : ℝ) (positive : 0 < t) (small : t < 1)
    {ε : ℝ} (εpositive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells,
                        Nonempty (R.RadialStripTraceData positive small D calibration i S
                          ε cutoff) := by
  classical
  have margins := fun i : FiveSector =>
    (fiveSectorFrame t positive small i).exists_enclosingStrip_coordinate_margin
  choose μ μpositive margin using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let c := min (min (μ j / 8) (1 / 8)) (ε / 2)
  have cpositive : 0 < c := lt_min
    (lt_min (div_pos (μpositive j) (by norm_num)) (by norm_num)) (by positivity)
  have csmall : c ≤ 1 / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have cε : 2 * c ≤ ε := by linarith [min_le_right (min (μ j / 8) (1 / 8)) (ε / 2)]
  have gap (i : FiveSector) : c * (1 + 2 * c) < μ i - 2 * c := by
    have left : c ≤ μ i / 8 := ((min_le_left _ _).trans (min_le_left _ _)).trans
      (div_le_div_of_nonneg_right (minimal i) (by norm_num))
    have bound : c * (1 + 2 * c) ≤ (5 / 4) * c := by nlinarith
    nlinarith
  obtain ⟨φ, bounds, normal, control⟩ :=
    exists_uniform_completed_frame_linear_error.{0, 0} t positive small cpositive
  refine ⟨φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have wedges := M.cornerExtendedOutward_curvedPathWedges positive small T internal source_height
    lower conforming height
  have roof_tilt : Q.TiltBound φ := L.partition.normalizedCap_tiltBound L.conforming lower tilt
  obtain ⟨budget, frames⟩ := control Q roof_tilt (K.projectedVertex origin)
    (M.extendedGeometricCuts F) R wedges
  have domains := M.cornerExtendedOutward_exists_regular_coherent_waterfall positive small T
    internal source_height lower conforming height cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨bankFrame, linear_error⟩ := frames (R.completedDevelopment D)
  let calibration := R.calibratedFrame (R.completedDevelopment D)
    bankFrame.anchor bankFrame.reference
  refine ⟨bankFrame, ?_⟩
  constructor
  · intro frame f z
    have estimate := linear_error frame f z
    have comparison : c ≤ ε := by linarith
    exact estimate.trans (mul_le_mul_of_nonneg_right comparison (norm_nonneg z))
  refine fun i => ?_
  obtain ⟨P, pinches, geometric, physical⟩ := domains i
  refine ⟨P, fun S cell => ?_⟩
  let B := fiveSectorFrame t positive small i
  let frame := B.place
  let E := insert (0 : ℂ) (Set.range (fun w :
    M.GeometricSectorLeaf F covered positive small lower i => w.point))
  have finite : E.Finite := (Set.finite_range (fun w :
    M.GeometricSectorLeaf F covered positive small lower i => w.point)).insert 0
  have root_source := B.enclosingStrip_source
  have source_bounds := P.cell_bounds cell 0
  rw [root_source.1, root_source.2] at source_bounds
  have ordered := S.ordered 0
  have first_source : S.lower.coordinate 0 = 0 :=
    le_antisymm (ordered.trans source_bounds.2) source_bounds.1
  have last_source : S.upper.coordinate 0 = 0 :=
    le_antisymm source_bounds.2 (source_bounds.1.trans ordered)
  have linear_bound (f) (z : ℂ) :
      ‖(D.coordinatePlacement Q calibration frame f).linear z‖ ≤ (2 : ℝ) * ‖z‖ := by
    have estimate := (D.coordinatePlacement_norm_bounds Q calibration frame f z).2
    have normal : (3 : ℝ) / 4 ≤ Q.normal f 2 := height (L.partition.face f)
    have product := mul_le_mul_of_nonneg_right normal
      (norm_nonneg ((D.coordinatePlacement Q calibration frame f).linear z))
    nlinarith [norm_nonneg z]
  have axes (f) (j) :
      0 < affineAxisMargins (D.coordinatePlacement Q calibration frame f).toAffineMap j :=
    affineAxisMargins_pos_of_linear_error (D.coordinatePlacement Q calibration frame f).toAffineMap
      (csmall.trans_lt (by norm_num)) (fun z => linear_error frame f z) j
  obtain ⟨G, continuous, equal, closed, traces⟩ := D.centeredMap_exists_injective_bank_trace
    (K.projectedVertex origin) calibration frame 2 linear_bound axes S E cutoff finite (Or.inl rfl)
    first_source last_source (pinches S cell) (physical D S cell)
  refine ⟨{
    coherentSet := E
    finite_coherentSet := finite
    source_mem := Or.inl rfl
    lower_source := first_source
    upper_source := last_source
    pinches := pinches S cell
    physical := physical D S cell
    avoids_cuts := fun z strict slab => (geometric S cell z strict slab).2
    value := G
    continuous := continuous
    equal := equal
    strict_injective := ?_
    closed_injective := closed
    radial := ?_
    bank_matching := ?_
    source_error := ?_
    traces := traces }⟩
  · exact D.centeredMap_injOn_strip_recoverable (K.projectedVertex origin) calibration frame
      axes S E 0 cutoff (pinches S cell) (physical D S cell)
  · intro active strict slab a d apositive before finish
    have visible := (traces active ⟨strict, slab⟩).2
    have on_wall (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper) (h : ℝ) :
        H.point h ∈ S.carrier := by
      rcases wall with rfl | rfl
      · change S.lower.coordinate ((S.lower.point h).re + (S.lower.point h).im) ≤
          (S.lower.point h).re ∧ (S.lower.point h).re ≤
          S.upper.coordinate ((S.lower.point h).re + (S.lower.point h).im)
        rw [S.lower.point_height]
        exact ⟨le_rfl, S.ordered h⟩
      · change S.lower.coordinate ((S.upper.point h).re + (S.upper.point h).im) ≤
          (S.upper.point h).re ∧ (S.upper.point h).re ≤
          S.upper.coordinate ((S.upper.point h).re + (S.upper.point h).im)
        rw [S.upper.point_height]
        exact ⟨S.ordered h, le_rfl⟩
    have radial (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper) :
        ‖G (H.point a) - D.centeredMap Q (K.projectedVertex origin) calibration frame 0‖ <
          ‖G (H.point d) - D.centeredMap Q (K.projectedVertex origin) calibration frame 0‖ := by
      have root : H.point a ∈ B.enclosingStrip.carrier :=
        (P.cover (H.point a)).mpr ⟨S, cell, on_wall H wall a⟩
      have forward : 0 ≤ (H.point a).re + (H.point a).im := by
        rw [H.point_height]
        exact apositive.le
      have coordinates := margin i (H.point a) root forward
      have size := B.enclosingStrip_forward_norm_bound root forward
      rw [H.point_height] at coordinates size
      apply D.centered_visible_heightGraph_radial Q (K.projectedVertex origin) calibration frame
        cpositive.le (fun f z => linear_error frame f z) S E first_source last_source
        (pinches S cell) (physical D S cell) continuous equal H apositive before (gap i)
        coordinates size
      intro h member
      have within : h ∈ Set.Icc 0 (active.re + active.im) :=
        ⟨apositive.le.trans member.1, member.2.trans finish⟩
      rcases wall with rfl | rfl
      · exact (visible h within).1
      · exact (visible h within).2
    exact ⟨radial S.lower (Or.inl rfl), radial S.upper (Or.inr rfl)⟩
  · apply R.matchesParentBanks_of_visible_traces positive small i (R.completedDevelopment D)
      calibration G S cutoff
    · intro z strict slab
      exact (geometric S cell z strict slab).2
    · intro z member slab regular k active width
      exact M.regular_waterfall_bank_width F covered positive small lower T i P S cell cutoff deep
        (pinches S cell) member slab regular active width
    · intro active strict slab h within
      exact (traces active ⟨strict, slab⟩).2 h within
  · intro z member slab
    have estimate := D.centeredMap_source_error (K := Q) (K.projectedVertex origin)
      calibration frame cpositive.le (fun f z => linear_error frame f z) S E first_source
      last_source (pinches S cell) (physical D S cell) member slab
    exact estimate.trans (mul_le_mul_of_nonneg_right cε slab.1)

end Unfoldings.ConvexCap
