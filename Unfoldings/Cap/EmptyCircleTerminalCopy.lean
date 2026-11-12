module

public import Unfoldings.Cap.EmptyCircleTerminalPinch
public import Unfoldings.Cap.CompletedTraceVertexCopy
public import Unfoldings.Geometry.AffineGraphPinches

/-! A disappearing actual strip terminates at its own cut-vertex contour copy inside the circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)

/-- The start copy is the face actually approached by the disappearing strip.
Other developed copies of this vertex remain distinct. -/
theorem exists_terminal_copy_of_empty_circle
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {radius : ℝ} (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ data.emptyCircleExceptions)
    (empty : data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅)
    (nonempty : (S.openSlab 0 cutoff).Nonempty) :
    ∃ h ∈ Set.Ioo (0 : ℝ) cutoff,
      (∀ k ∈ Set.Icc h cutoff, S.lower.coordinate k = S.upper.coordinate k) ∧
      S.lower.point h ∈ closure (S.openSlab 0 cutoff) ∧
      S.upper.point h ∈ closure (S.openSlab 0 cutoff) ∧
      ‖data.value (S.lower.point h) - data.center‖ < radius ∧
      ∃ w : C.Vertex Set.univ, K.projectedVertex w ∈ cuts ∧
        source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
          K.projectedVertex w ∧
        ∃ target : Fin (N.completedContour.length + 1),
          C.vertexForgetCuts (Set.subset_univ _)
            (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = w ∧
          data.value (S.lower.point h) =
            B.sectorFrame i ((N.completedDevelopment D).boundaryPosition
              (N.completedContour.cycle.point target)) := by
  obtain ⟨h, bounds, merged, first, last, near, visible, _⟩ :=
    data.exists_terminal_pinch_of_empty_circle radius_positive far outside empty nonempty
  have approached : S.lower.point h ∈ closure S.strictCarrier :=
    closure_mono (fun _ member => member.1) first
  obtain ⟨w, at_point⟩ := pinches h bounds (merged h ⟨le_rfl, bounds.2.le⟩) approached
  have physical : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
      K.projectedVertex w.val := by
    change (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source) =
      S.lower.point h at at_point
    rw [← at_point, LinearIsometryEquiv.symm_apply_apply]
    abel
  have completed_visible : (N.completedDevelopment D).TraceVisibleAt K source
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference)
      (fiveSectorFrame t positive small i).place data.value data.strictDomain (S.lower.point h) :=
    visible
  obtain ⟨target, original, value⟩ :=
    B.trace_vertex_is_boundary_copy i w.val completed_visible physical
  exact ⟨h, bounds, merged, first, last, near, w.val, w.property, physical,
    target, original, value⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
