module

public import Unfoldings.Cap.CompletedBankFaceValues
public import Unfoldings.Cap.FacePositionMargins

/-! Common-source error and quadrant bounds apply to the actual complete bank points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem framed_projectedPlacement_source_error_eq (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ) (f : Face) (p : Plane) :
    let output := calibration.trans (Complex.orthonormalBasisOneI.repr.trans frame)
    ‖output (D.projectedPlacement K f p - D.projectedMap K q) - frame (p - q)‖ =
      ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K q)) -
        Complex.orthonormalBasisOneI.repr.symm (p - q)‖ := by
  let L := Complex.orthonormalBasisOneI.repr.trans frame
  change ‖L (calibration (D.projectedPlacement K f p - D.projectedMap K q)) -
    frame (p - q)‖ = _
  have vector : frame (p - q) = L (Complex.orthonormalBasisOneI.repr.symm (p - q)) := by
    change frame (p - q) = frame
      (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm (p - q)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [vector, ← L.map_sub, L.norm_map, calibration.map_sub]

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  (D : FacewiseDevelopment C N.completedRetain)

theorem parent_bank_source_error (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    {s : ℝ} (inside : s ∈ Set.Icc 0 1) (ε : ℝ)
    (control : ∀ f, ∀ p ∈ (K.projectedTriangle f).carrier,
      p = AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) s →
      ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K source)) -
        Complex.orthonormalBasisOneI.repr.symm (p - source)‖ ≤ ε * ‖p - source‖) :
    let p := AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s
    let output := calibration.trans (Complex.orthonormalBasisOneI.repr.trans frame)
    ‖output (N.parentEntrancePoint D e s - D.projectedMap K source) - frame (p - source)‖ ≤
        ε * ‖p - source‖ ∧
      ‖output (N.parentExitPoint D e s - D.projectedMap K source) - frame (p - source)‖ ≤
        ε * ‖p - source‖ := by
  have members := N.parent_bank_points_mem_faces D e inside
  dsimp only
  rw [N.parentEntrancePoint_eq_projectedPlacement, N.parentExitPoint_eq_projectedPlacement,
    D.framed_projectedPlacement_source_error_eq K,
    D.framed_projectedPlacement_source_error_eq K]
  exact ⟨control _ _ members.1 rfl, control _ _ members.2 rfl⟩

theorem parent_bank_quadrant_margin (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    (e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    {s : ℝ} (inside : s ∈ Set.Icc 0 1) (ε μ : ℝ)
    (horizontal : μ * ‖AffineMap.lineMap
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s - source‖ ≤ (frame (AffineMap.lineMap
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s - source)).re)
    (vertical : μ * ‖AffineMap.lineMap
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s - source‖ ≤ (frame (AffineMap.lineMap
      (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s - source)).im)
    (control : ∀ f, ∀ p ∈ (K.projectedTriangle f).carrier,
      p = AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
        (K.projectedVertex e.val) s →
      ‖(calibration (D.projectedPlacement K f p) - calibration (D.projectedMap K source)) -
        Complex.orthonormalBasisOneI.repr.symm (p - source)‖ ≤ ε * ‖p - source‖) :
    let p := AffineMap.lineMap (K.projectedVertex (N.spanningCompletion.parents.parent e.val))
      (K.projectedVertex e.val) s
    let output := calibration.trans (Complex.orthonormalBasisOneI.repr.trans frame)
    ((μ - ε) * ‖p - source‖ ≤
      (output (N.parentEntrancePoint D e s - D.projectedMap K source)).re ∧
      (μ - ε) * ‖p - source‖ ≤
        (output (N.parentEntrancePoint D e s - D.projectedMap K source)).im) ∧
    ((μ - ε) * ‖p - source‖ ≤
      (output (N.parentExitPoint D e s - D.projectedMap K source)).re ∧
      (μ - ε) * ‖p - source‖ ≤
        (output (N.parentExitPoint D e s - D.projectedMap K source)).im) := by
  have error := N.parent_bank_source_error D calibration frame e inside ε control
  have bound (w z : ℂ) (r : ℝ) (re : μ * r ≤ z.re) (im : μ * r ≤ z.im)
      (near : ‖w - z‖ ≤ ε * r) :
      (μ - ε) * r ≤ w.re ∧ (μ - ε) * r ≤ w.im := by
    have first := (abs_le.mp ((Complex.abs_re_le_norm _).trans near)).1
    have last := (abs_le.mp ((Complex.abs_im_le_norm _).trans near)).1
    simp only [Complex.sub_re] at first
    simp only [Complex.sub_im] at last
    constructor <;> nlinarith
  exact ⟨bound _ _ _ horizontal vertical error.1, bound _ _ _ horizontal vertical error.2⟩

end Unfoldings.ConvexCap.RadialCutForest
