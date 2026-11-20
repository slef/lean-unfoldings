module

public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofLayout
public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps
public import Unfoldings.Roof.CompatibleOriginalDevelopment
public import Unfoldings.Roof.CompatibleComponentCutDisk

/-! A uniform original-edge development of each selected whole-face component. -/

@[expose] public section

noncomputable section

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

include no_boundary level higher positive inner_disk beta acute

open Classical in
set_option maxHeartbeats 2500000 in
-- Specialize the global layout and exact original-face identities to each selected component.
/-- Under the uniform angle and tilt bounds, each selected normal component has
a disk cut along the original selected seams and a nonoverlapping development of
its original input triangles. -/
theorem exists_uniform_compatible_component_original_edge_development
    (convex : Convex ℝ slopes) {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b)
    (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
    (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ ψ ∈ Set.Ioc (0 : ℝ) θ,
      (∀ i, Real.cos ψ ≤ (M.plane i).normal 2) →
      ∀ seed, K.normalSlope seed ∈ slopes →
        let U := K.selectionComponent slopes seed
        let T := C.restrictFaces U
        let retain := C.restrictRetain U (C.selectedRetain R.original.selection)
        Nonempty (T.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
          ∃ D : FacewiseDevelopment T retain, D.Nonoverlapping := by
  obtain ⟨θ, tilt, gaps⟩ := K.exists_uniform_contourSourceOnlyGap_geometry compact nonempty R
    no_boundary level higher M positive inner_disk beta acute bpos ratio upper small
  obtain ⟨contour, starts, ends, _⟩ := K.exists_compatibleMesh_completeSourceContour
    compact nonempty R no_boundary level higher positive inner_disk beta acute M convex
  let W := R.wholeCutModel M
  refine ⟨θ, tilt, fun ψ hψ normal => ?_⟩
  let atTilt e := gaps ψ hψ normal contour starts e
  obtain ⟨layout, cont, faithful, local_iso⟩ :=
    K.compatibleContourSourceOnlyGraft_exists_roof_layout compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W (fun e => (atTilt e).1)
      convex ends (fun e k => ((atTilt e).2 k).1)
  intro seed selected
  refine ⟨K.exists_compatible_component_cut_disk convex compact.isClosed seed selected
    R.original, ?_⟩
  exact K.exists_original_development_of_compatible_roof_layout compact nonempty R no_boundary M W
    (K.selectionComponent slopes seed) (fun _ hf => K.selectionComponent_selected selected hf)
    layout cont faithful local_iso

end Unfoldings.ConvexRoof
