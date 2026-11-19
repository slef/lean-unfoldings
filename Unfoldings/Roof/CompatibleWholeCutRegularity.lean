module

public import Unfoldings.Roof.CompatibleMeshWindowCharts
public import Unfoldings.Roof.SpatialEnvelopeCap
public import Unfoldings.Polyhedron.BoundaryAwayFromCuts
public import Unfoldings.Development.FlatDisk
public import Unfoldings.Metric.LocalBallRegularity

/-! Actual finite cut meshes derive intrinsic regularity of the whole roof away from its forest. -/

@[expose] public section

noncomputable section

open scoped ENNReal

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance compatibleOffCutIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include higher positive inner_disk beta acute no_boundary

/-- Below the actual rim level, a finite mesh copy outside the physical forest is not
on the cut boundary. Newly created banks lie over cuts, and original banks lie at the rim. -/
theorem compatibleMesh_off_cut_not_bankBoundary
    (x : (T).pairedComplex.Realization (Fcut).retain)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x)) < level)
    (off_cut : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x) ∉ R.carrier) :
    x ∉ (T).pairedComplex.bankBoundary (Fcut).retain := by
  intro member
  obtain ⟨bank, z, rfl⟩ := Set.mem_iUnion.mp member
  have position : (T).pairedFolding.toSpace (Fcut).retain
      ((T).pairedComplex.bankMap (Fcut).retain bank z) =
        (T).placement bank.val.face z.val := rfl
  have original := (T).pairedFolding.boundaryBank_original_of_outside (Fcut).retain
    (Cap.horizontal ⁻¹' R.carrier)
    (K.compatibleMesh_removed_edge compact nonempty R no_boundary level higher M positive
      inner_disk beta acute) bank z off_cut
  have at_rim := (T).toTriangulation.bank_height conforming inside ⟨bank.val, original⟩ z
  have graph : (T).placement bank.val.face z.val 2 =
      SpatialEnvelope.height M.plane (Cap.horizontal ((T).placement bank.val.face z.val)) := by
    rw [(T).toTriangulation.placement_eq_point bank.val.face
      (((T).triangle bank.val.face).edge_subset bank.val.edge z.property),
      SpatialEnvelope.height_point, SpatialEnvelope.horizontal_point]
  have height := graph.trans (M.height_eq _)
  have near : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).placement bank.val.face z.val)) < level :=
    (congrArg (fun p => (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal p)) position).symm.trans_lt below
  linarith

/-- The constructed flat disk gives genuine intrinsic planar regularity at every finite
mesh copy below the rim and outside the original physical forest. -/
theorem compatibleMesh_off_cut_regular (convex : Convex ℝ slopes)
    (x : (T).pairedComplex.Realization (Fcut).retain)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x)) < level)
    (off_cut : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain x) ∉ R.carrier) :
    (T).pairedComplex.IsRegularPoint (Fcut).retain x := by
  have outside_boundary := K.compatibleMesh_off_cut_not_bankBoundary compact nonempty R no_boundary
    level higher M positive inner_disk beta acute x below off_cut
  have norm_ne : ‖((Fcut).cutDisk x).val‖ ≠ 1 := fun equal => outside_boundary
    (((T).pairedFolding.bankBoundary_iff_disk_norm_eq_one (Fcut).retain (Fcut).cutDisk x).mpr equal)
  have norm_le : ‖((Fcut).cutDisk x).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ((Fcut).cutDisk x).property
  exact (T).pairedFolding.isRegularPoint_of_flat_disk (Fcut).retain (Fcut).cutDisk
    (K.compatibleMeshCut_interior_flat compact nonempty R no_boundary level higher M positive
      inner_disk beta acute convex) x (lt_of_le_of_ne norm_le norm_ne)

variable (W : R.WholeCutModel M)

local instance wholeCutRegularIndexFintype : Fintype W.Index := W.finiteIndex

/-- Intrinsic whole-roof regularity below a completion level is derived from the actual
finite cut mesh and its whole-ball inclusion, not supplied as a local chart certificate. -/
theorem compatibleWholeCut_below_off_cut_regular (convex : Convex ℝ slopes)
    (x : W.Cut)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < level)
    (off_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∉ R.carrier) :
    HasMetricBallChart Plane x := by
  obtain ⟨source, at_x, r, rpos, B, agrees⟩ := K.exists_compatibleMesh_ball_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W x below
  have physical : (T).pairedFolding.toSpace (Fcut).retain source =
      (W.partition.restoreCut R.carrier x).val :=
    (K.restore_compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W source).symm.trans
      (congrArg (fun y => (W.partition.restoreCut R.carrier y).val) at_x)
  have source_below := (congrArg (fun p => (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal p)) physical).trans_lt below
  have source_outside : Cap.horizontal ((T).pairedFolding.toSpace (Fcut).retain source) ∉
      R.carrier := by
    intro member
    exact off_cut ((congrArg Cap.horizontal physical) ▸ member)
  have regular : HasMetricBallChart Plane source :=
    K.compatibleMesh_off_cut_regular compact nonempty R no_boundary level higher M positive
      inner_disk beta acute convex source source_below source_outside
  have center : (B ⟨source, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val = x :=
    (agrees _).trans at_x
  exact regular.of_centered_ball_equiv rpos B center

/-- Increasing the completion level covers every original whole-roof point outside the
forest, including points on unbounded cells and original roof cell seams. -/
theorem compatibleWholeCut_off_cut_regular (convex : Convex ℝ slopes)
    (x : W.Cut) (off_cut : Cap.horizontal (W.partition.restoreCut R.carrier x).val ∉ R.carrier) :
    HasMetricBallChart Plane x := by
  let L := max level ((K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut R.carrier x).val) + 1)
  have higher_L : ∀ v, (K.clippedExtension slopes compact nonempty).height
      (K.projectedVertex v) < L := fun v => (higher v).trans_le (le_max_left _ _)
  have below_L : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier x).val) < L :=
    (lt_add_one _).trans_le (le_max_right _ _)
  exact K.compatibleWholeCut_below_off_cut_regular compact nonempty R no_boundary L higher_L M
    positive inner_disk beta acute W convex x below_L off_cut

end Unfoldings.ConvexRoof
