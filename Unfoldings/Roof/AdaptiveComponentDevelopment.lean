module

public import Unfoldings.Roof.AdaptiveContourGap
public import Unfoldings.Roof.AdaptiveComponentCutDisk
public import Unfoldings.Roof.CompatibleComponentDevelopment
public import Unfoldings.Development.NetPartition

/-! Complete nonoverlapping developments of original-edge adaptive roof components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

set_option maxHeartbeats 2500000 in
open Classical in
/-- At the actual tilt, the sharp radial-block estimate supports the complete
source-by-source gluing. Each selected component unfolds along original seams. -/
theorem hasOriginalEdgeNet_of_adaptiveRouting
    (K : ConvexRoof C) {slopes : Set Plane} (convex : Convex ℝ slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    {boundary : (frontier slopes).Nonempty} {L : Set Plane} {r margin η : ℝ}
    (R : K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary L r margin η)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
    (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    {φ γ A : ℝ} (tilt_pos : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (normal : ∀ i, cos φ ≤ (M.plane i).normal 2)
    (gamma_pos : 0 < γ) (gamma_le : γ ≤ 1) (interior_margin : γ ≤ margin)
    (exterior_margin : γ ≤ η) (length_bound : b / r ≤ A)
    (small : radialBlockError (cos φ)⁻¹ (shallowDevelopmentHeading φ) A
      (sqrt (1 - γ ^ 2)) π < γ) :
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  let common := R.asCommonPotentialRouting positive disk bound_pos ratio upper
  let inner_disk : Metric.ball (0 : Plane) r ⊆ slopes :=
    Metric.ball_subset_closedBall.trans (disk.trans R.within)
  let βnonneg : 0 ≤ arccos (r / b) := arccos_nonneg _
  let βacute : arccos (r / b) < π / 2 := arccos_lt_pi_div_two.mpr (div_pos positive bound_pos)
  obtain ⟨level, higher⟩ := CompatiblePotentialRouting.exists_truncation_level
    (K := K) (G := K.clippedExtension slopes compact nonempty)
  obtain ⟨contour, starts, ends, _⟩ := K.exists_compatibleMesh_completeSourceContour
    compact nonempty common no_boundary level higher positive inner_disk βnonneg βacute M convex
  let W := common.wholeCutModel M
  let geometry e := K.adaptiveContourSourceOnly_gap compact nonempty R no_boundary level higher
    M positive disk bound_pos ratio upper tilt_pos small_phi height_bound normal gamma_pos
    gamma_le interior_margin exterior_margin length_bound small contour starts e
  obtain ⟨layout, cont, faithful, local_iso⟩ :=
    K.compatibleContourSourceOnlyGraft_exists_roof_layout compact nonempty common no_boundary
      level higher M positive inner_disk βnonneg βacute contour starts W
      (fun e => (geometry e).1) convex ends (fun e => (geometry e).2)
  intro seed selected
  let U := K.selectionComponent slopes seed
  refine ⟨C.restrictRetain U (C.selectedRetain common.original.selection), ?_, ?_⟩
  · exact K.exists_compatible_component_cut_disk convex compact.isClosed seed selected common.original
  · exact K.exists_original_development_of_compatible_roof_layout compact nonempty common
      no_boundary M W U (fun _ hf => K.selectionComponent_selected selected hf)
      layout cont faithful local_iso

end Unfoldings.ConvexRoof
