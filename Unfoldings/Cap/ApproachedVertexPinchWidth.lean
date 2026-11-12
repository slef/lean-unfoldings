module

public import Unfoldings.Cap.RadialStripTraceVisibility
public import Unfoldings.Geometry.AffineGraphPinches

/-! A regular approached bank point has positive width, even below a terminal pinch. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- The actual vertex-pinch classification excludes collapsed width at every
regular point of the approached strip, without requiring a later active height. -/
theorem width_pos_of_approached_regular
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (closed : S.lower.point h ∈ closure data.strictDomain)
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point h) ≠ (K.projectedTriangle f).vertex j) :
    S.lower.coordinate h < S.upper.coordinate h := by
  by_contra collapsed
  have equal : S.lower.coordinate h = S.upper.coordinate h :=
    le_antisymm (S.ordered h) (not_lt.mp collapsed)
  have approached : S.lower.point h ∈ closure S.strictCarrier :=
    closure_mono (fun _ member => member.1) closed
  obtain ⟨w, at_vertex⟩ := pinches h height equal approached
  have physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point h) = K.projectedVertex w.val := by
    rw [← at_vertex, LinearIsometryEquiv.symm_apply_apply]
    abel
  obtain ⟨⟨f, j⟩, original⟩ := C.vertexOfCorner_surjective Set.univ w.val
  apply regular f j
  rw [physical, ← original]
  rfl

/-- The same regularity test applies to the upper bank. -/
theorem width_pos_of_upper_approached_regular
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (pinches : S.ApproachedPinchesIn
      (Set.range (fun w : {w : C.Vertex Set.univ // K.projectedVertex w ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex w.val - source))) 0 cutoff)
    {h : ℝ} (height : h ∈ Set.Ioo 0 cutoff)
    (closed : S.upper.point h ∈ closure data.strictDomain)
    (regular : ∀ f j, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point h) ≠ (K.projectedTriangle f).vertex j) :
    S.lower.coordinate h < S.upper.coordinate h := by
  by_contra collapsed
  have equal : S.lower.coordinate h = S.upper.coordinate h :=
    le_antisymm (S.ordered h) (not_lt.mp collapsed)
  have points := S.lower.point_eq_of_same_coordinate S.upper equal
  have lower_closed : S.lower.point h ∈ closure data.strictDomain := by
    rw [points]
    exact closed
  exact collapsed (data.width_pos_of_approached_regular pinches height lower_closed
    (by rw [points]; exact regular))

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
