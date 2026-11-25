module

public import Unfoldings.FewestNets.ThreeExitMeshWindow
public import Unfoldings.Geometry.SpatialEnvelopePartitionIndependence
public import Unfoldings.Polyhedron.BoundaryAwayFromCuts
public import Unfoldings.Development.FlatDisk
public import Unfoldings.Roof.AffineFloorCutBoundary
public import Unfoldings.Metric.LocalBallRegularity
public import Unfoldings.Metric.BallChartTransport

/-! Interior flatness of the actual whole three-exit cut outside the forest. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty}
  {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "G₀" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "G" => SlopeEnvelope.recenter (G₀) B.reference

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}

local notation "T[" h "]" => R.fineMesh level M h
local notation "Fcut[" h "]" => R.fineMeshForest level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "Fold[" h "]" => SpatialEnvelope.FloorMesh.pairedFolding T[h]
local notation "Retain[" h "]" => PotentialCutForest.retain Fcut[h]

local instance regularVertexFintype : Fintype V := Fintype.ofFinite V

local instance meshIndexFintype (h : ∀ v : V, (G).height (p v) < level) :
    Fintype (R.fineMesh level M h).Index := @Fintype.ofFinite _ (R.fineMesh level M h).finite

/-- Below the affine rim, every mesh boundary copy projects onto the prescribed cut. -/
theorem fineMesh_off_cut_not_bankBoundary
    (higher : ∀ v : V, (G).height (p v) < level) (x : (D[higher]).Realization Retain[higher])
    (below : (G).height (Cap.horizontal ((Fold[higher]).toSpace Retain[higher] x)) < level)
    (outside : Cap.horizontal ((Fold[higher]).toSpace Retain[higher] x) ∉ R.wholeCarrier) :
    x ∉ (D[higher]).bankBoundary Retain[higher] := by
  intro member
  obtain ⟨bank, z, named⟩ := Set.mem_iUnion.mp member
  have position : Cap.horizontal ((Fold[higher]).place bank.val.face z.val) =
      Cap.horizontal ((Fold[higher]).toSpace Retain[higher] x) :=
    congrArg (fun y => Cap.horizontal ((Fold[higher]).toSpace Retain[higher] y)) named
  have original := (Fold[higher]).boundaryBank_original_of_outside Retain[higher]
    (Cap.horizontal ⁻¹' R.wholeCarrier) (R.fineMesh_removed_edge level M higher)
    bank z (fun hx => outside (position ▸ hx))
  have at_rim := (T[higher]).projected_original_bank_frontier
    (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
    ⟨bank.val, original⟩ z
  exact at_rim.2 (by
    rw [M.clipAbove_referenceFloor_eq]
    rw [position]
    exact (G).mem_interior_sublevel below)

/-- The finite mesh cut has an intrinsic planar ball at each off-cut point below the rim. -/
theorem fineMesh_off_cut_regular
    (higher : ∀ v : V, (G).height (p v) < level) (x : (D[higher]).Realization Retain[higher])
    (below : (G).height (Cap.horizontal ((Fold[higher]).toSpace Retain[higher] x)) < level)
    (outside : Cap.horizontal ((Fold[higher]).toSpace Retain[higher] x) ∉ R.wholeCarrier) :
    HasMetricBallChart Plane x := by
  have outside_bank := R.fineMesh_off_cut_not_bankBoundary higher x below outside
  have norm_ne : ‖((Fcut[higher]).cutDisk x).val‖ ≠ 1 := fun equal => outside_bank
    (((Fold[higher]).bankBoundary_iff_disk_norm_eq_one Retain[higher] (Fcut[higher]).cutDisk x).mpr equal)
  have norm_le : ‖((Fcut[higher]).cutDisk x).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ((Fcut[higher]).cutDisk x).property
  exact (Fold[higher]).isRegularPoint_of_flat_disk Retain[higher] (Fcut[higher]).cutDisk
    ((Fcut[higher]).interior_flat (R.fineMesh_curvature_covered level M higher)) x
    (lt_of_le_of_ne norm_le norm_ne)

namespace FloorWindowModel

variable {R} (L : R.FloorWindowModel level M)

/-- Transfer finite interior balls to the actual complete roof below this floor window. -/
theorem wholeCut_below_off_cut_regular (higher : ∀ v : V, (G).height (p v) < level)
    (x : L.whole.Cut)
    (below : (G).height (Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val) < level)
    (outside : Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val ∉ R.wholeCarrier) :
    HasMetricBallChart Plane x := by
  obtain ⟨y, mapped, r, r_pos, chart, agrees⟩ := L.exists_fineMesh_ball_chart higher x below
  have physical : (Fold[higher]).toSpace Retain[higher] y =
      (L.whole.partition.restoreCut R.wholeCarrier x).val :=
    (L.restore_fineMeshWholeMap higher y).symm.trans
      (congrArg (fun z => (L.whole.partition.restoreCut R.wholeCarrier z).val) mapped)
  have regular := R.fineMesh_off_cut_regular higher y
    (by rw [physical]; exact below) (by rw [physical]; exact outside)
  exact regular.of_centered_ball_equiv r_pos chart ((agrees _).trans mapped)

private theorem outside_wholeCut (i : L.whole.Index) :
    Disjoint (interior (L.whole.partition.footprint i)) R.wholeCarrier := by
  apply Set.disjoint_left.mpr
  intro x inside cut
  obtain ⟨j, zero⟩ := R.wholeCarrier_covered_by_equations cut
  exact not_mem_interior_of_affine_lower_bound
    (AffineArrangement.signed (R.wholeCutEquation j) (L.whole.signs i j))
    (AffineArrangement.signed_ne_zero _ (R.wholeCutEquation_ne_zero j) _)
    (fun z hz => L.whole.aligned i z hz j)
    ((AffineArrangement.signed_eq_zero_iff _ _ _).mpr zero) inside

set_option maxHeartbeats 1000000 in
/-- Any off-cut point of the complete roof is inside some finite window.
Changing the window preserves the physical marked point and its metric. -/
theorem wholeCut_off_cut_regular (higher : ∀ v : V, (G).height (p v) < level)
    (x : L.whole.Cut)
    (outside : Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val ∉ R.wholeCarrier) :
    HasMetricBallChart Plane x := by
  let z := Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val
  let larger := max level ((G).height z + 1)
  have higher_large : ∀ v : V, (G).height (p v) < larger :=
    fun v => (higher v).trans_le (le_max_left _ _)
  let W := R.floorWindowModel larger M higher_large
  let e := L.whole.partition.cutPartitionEquiv W.whole.partition R.wholeCarrier
    R.isClosed_wholeCarrier L.outside_wholeCut W.outside_wholeCut
  have position := L.whole.partition.restoreCut_cutPartitionEquiv W.whole.partition R.wholeCarrier
    R.isClosed_wholeCarrier L.outside_wholeCut W.outside_wholeCut x
  apply (hasMetricBallChart_isometryEquiv_iff e x).mp
  change HasMetricBallChart Plane (L.whole.partition.cutPartitionEquiv W.whole.partition R.wholeCarrier
    R.isClosed_wholeCarrier L.outside_wholeCut W.outside_wholeCut x)
  apply W.wholeCut_below_off_cut_regular higher_large
  · rw [position]
    exact (lt_add_one _).trans_le (le_max_right _ _)
  · rw [position]
    exact outside

end FloorWindowModel
end Unfoldings.ConvexRoof.ThreeExitComponentRouting
