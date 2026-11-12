module

public import Unfoldings.Cap.RadialStripTraceVisibility

/-! One finite exceptional radius set excludes every vertex value of all actual strip traces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- All containing-face copies are included. The definition is independent of
strip choices and does not identify distinct developed copies of one vertex. -/
def fiveSectorVertexRadii (K : ConvexCap C) (source : Plane)
    (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {t : ℝ} (positive : 0 < t) (small : t < 1) : Set ℝ :=
  Set.range (fun a : FiveSector × Face × C.Vertex Set.univ =>
    let frame := (fiveSectorFrame t positive small a.1).place
    ‖D.centeredCoordinatePlacement K source calibration frame a.2.1
        (frame (K.projectedVertex a.2.2 - source)) -
      D.centeredMap K source calibration frame 0‖)

theorem finite_fiveSectorVertexRadii (K : ConvexCap C) (source : Plane)
    (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {t : ℝ} (positive : 0 < t) (small : t < 1) :
    (D.fiveSectorVertexRadii K source calibration positive small).Finite := Set.finite_range _

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

/-- Every approached strip point on a nonexceptional circle is physically regular.
The finite set covers all sectors and every actual incident-face copy at once. -/
theorem regular_of_radius_not_vertexRadii
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    {radius : ℝ} (outside : radius ∉ D.fiveSectorVertexRadii K source calibration positive small)
    {z : ℂ} (closed : z ∈ closure data.strictDomain)
    (size : ‖data.value z - data.center‖ = radius) :
    ∀ g j, source + (fiveSectorFrame t positive small i).place.symm z ≠
      (K.projectedTriangle g).vertex j := by
  let frame := (fiveSectorFrame t positive small i).place
  obtain ⟨f, _, _, value⟩ := data.visible_closure closed
  intro g j equal
  let w := C.vertexOfCorner Set.univ (g, j)
  have physical : source + frame.symm z = K.projectedVertex w := equal
  have inverse : frame.symm z = K.projectedVertex w - source := by
    rw [← physical]
    abel
  have input : z = frame (K.projectedVertex w - source) := by
    simpa only [frame.apply_symm_apply] using congrArg frame inverse
  apply outside
  refine ⟨(i, f, w), ?_⟩
  change ‖D.centeredCoordinatePlacement K source calibration frame f
      (frame (K.projectedVertex w - source)) -
    D.centeredMap K source calibration frame 0‖ = radius
  rw [← input, ← value]
  exact size

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
