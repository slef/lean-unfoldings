module

public import Unfoldings.Cap.CenteredTraceValues
public import Unfoldings.Cap.ProjectedSeamFaces
public import Unfoldings.Geometry.StripCutSides

/-! One-sided face visibility identifies the actual facing chart at a regular cut edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- An open one-sided approach cannot contribute a face lying on the opposite closed side.
Only the local domain near the bank point needs to lie strictly on the chosen side. -/
theorem traceVisibleAt_eq_of_local_side (q : Plane) (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z)
    (f g : Face)
    (faces : ∀ h, q + frame.symm z ∈ (K.projectedTriangle h).carrier → h = f ∨ h = g)
    (height : ℂ → ℝ) (U : Set ℂ) (opened : IsOpen U) (near : z ∈ U)
    (positive : ∀ x ∈ domain ∩ U, 0 < height x)
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle g).carrier → height x ≤ 0) :
    G z = D.centeredCoordinatePlacement K q calibration frame f z := by
  obtain ⟨h, member, approach, value⟩ := trace
  rcases faces h member with first | last
  · rw [first] at value
    exact value
  · subst h
    have disjoint : Disjoint U
        (domain ∩ {x | q + frame.symm x ∈ (K.projectedTriangle g).carrier}) := by
      apply Set.disjoint_left.mpr
      intro x in_U in_domain
      exact not_lt_of_ge (opposite x in_domain.2) (positive x ⟨in_domain.1, in_U⟩)
    exact (Set.disjoint_left.mp (disjoint.closure_right opened) near approach).elim

theorem traceVisibleAt_eq_left_of_seam_side (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (height : ℂ → ℝ) (U : Set ℂ) (opened : IsOpen U) (near : z ∈ U)
    (positive : ∀ x ∈ domain ∩ U, 0 < height x)
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.right s).face).carrier →
      height x ≤ 0) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.left s).face z := by
  exact D.traceVisibleAt_eq_of_local_side K q calibration frame trace
    (C.left s).face (C.right s).face
    (fun _ member => K.projected_face_eq_seamSide_of_regular s on_edge member regular)
    height U opened near positive opposite

theorem traceVisibleAt_eq_right_of_seam_side (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (height : ℂ → ℝ) (U : Set ℂ) (opened : IsOpen U) (near : z ∈ U)
    (positive : ∀ x ∈ domain ∩ U, 0 < height x)
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.left s).face).carrier →
      height x ≤ 0) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.right s).face z := by
  exact D.traceVisibleAt_eq_of_local_side K q calibration frame trace
    (C.right s).face (C.left s).face
    (fun _ member => (K.projected_face_eq_seamSide_of_regular s on_edge member regular).symm)
    height U opened near positive opposite

/-- A wall needs to agree with the physical edge graph only in a height neighborhood.
Strict strip membership supplies the one-sided approach automatically. -/
theorem traceVisibleAt_eq_left_of_lower_wall (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (S : MonotoneStrip) (H : MonotoneHeightGraph) (a b : ℝ)
    (strict : domain ⊆ S.strictCarrier) (near : z.re + z.im ∈ Set.Ioo a b)
    (wall : Set.EqOn S.lower.coordinate H.coordinate (Set.Ioo a b))
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.right s).face).carrier →
      x.re ≤ H.coordinate (x.re + x.im)) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.left s).face z := by
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo a b}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_left_of_seam_side K q calibration frame trace s on_edge regular
    (fun x => x.re - H.coordinate (x.re + x.im)) U opened near
  · intro x member
    rw [← wall member.2]
    exact sub_pos.mpr (strict member.1).1
  · intro x member
    exact sub_nonpos.mpr (opposite x member)

theorem traceVisibleAt_eq_right_of_upper_wall (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (S : MonotoneStrip) (H : MonotoneHeightGraph) (a b : ℝ)
    (strict : domain ⊆ S.strictCarrier) (near : z.re + z.im ∈ Set.Ioo a b)
    (wall : Set.EqOn S.upper.coordinate H.coordinate (Set.Ioo a b))
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.left s).face).carrier →
      H.coordinate (x.re + x.im) ≤ x.re) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.right s).face z := by
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo a b}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_right_of_seam_side K q calibration frame trace s on_edge regular
    (fun x => H.coordinate (x.re + x.im) - x.re) U opened near
  · intro x member
    rw [← wall member.2]
    exact sub_pos.mpr (strict member.1).2
  · intro x member
    exact sub_nonpos.mpr (opposite x member)

/-- Positive width and actual cut avoidance supply the side test even when the wall
merely touches the cut graph. There is no local wall-coincidence hypothesis. -/
theorem traceVisibleAt_eq_left_of_lower_cut (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (S : MonotoneStrip) (H : MonotoneHeightGraph) (a b : ℝ)
    (strict : domain ⊆ S.strictCarrier) (near : z.re + z.im ∈ Set.Ioo a b)
    (on_wall : S.lower.coordinate (z.re + z.im) = z.re)
    (touch : H.coordinate (z.re + z.im) = z.re)
    (width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im))
    (avoids : ∀ k ∈ Set.Ioo a b, H.point k ∉ S.strictCarrier)
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.right s).face).carrier →
      x.re ≤ H.coordinate (x.re + x.im)) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.left s).face z := by
  obtain ⟨c, d, around, _, side⟩ := S.cut_below_lower_locally H near
    (touch.trans on_wall.symm) width avoids
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo c d}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_left_of_seam_side K q calibration frame trace s on_edge regular
    (fun x => x.re - H.coordinate (x.re + x.im)) U opened around
  · intro x member
    exact sub_pos.mpr ((side _ member.2).trans_lt (strict member.1).1)
  · intro x member
    exact sub_nonpos.mpr (opposite x member)

theorem traceVisibleAt_eq_right_of_upper_cut (q : Plane)
    (calibration frame : Plane ≃ₗᵢ[ℝ] ℂ)
    {G : ℂ → ℂ} {domain : Set ℂ} {z : ℂ}
    (trace : D.TraceVisibleAt K q calibration frame G domain z) (s : C.Seam)
    (on_edge : q + frame.symm z ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (regular : ∀ f j, q + frame.symm z ≠ (K.projectedTriangle f).vertex j)
    (S : MonotoneStrip) (H : MonotoneHeightGraph) (a b : ℝ)
    (strict : domain ⊆ S.strictCarrier) (near : z.re + z.im ∈ Set.Ioo a b)
    (on_wall : S.upper.coordinate (z.re + z.im) = z.re)
    (touch : H.coordinate (z.re + z.im) = z.re)
    (width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im))
    (avoids : ∀ k ∈ Set.Ioo a b, H.point k ∉ S.strictCarrier)
    (opposite : ∀ x, q + frame.symm x ∈ (K.projectedTriangle (C.left s).face).carrier →
      H.coordinate (x.re + x.im) ≤ x.re) :
    G z = D.centeredCoordinatePlacement K q calibration frame (C.right s).face z := by
  obtain ⟨c, d, around, _, side⟩ := S.cut_above_upper_locally H near
    (touch.trans on_wall.symm) width avoids
  let U := {x : ℂ | x.re + x.im ∈ Set.Ioo c d}
  have opened : IsOpen U := isOpen_Ioo.preimage
    (Complex.continuous_re.add Complex.continuous_im)
  apply D.traceVisibleAt_eq_right_of_seam_side K q calibration frame trace s on_edge regular
    (fun x => H.coordinate (x.re + x.im) - x.re) U opened around
  · intro x member
    exact sub_pos.mpr ((strict member.1).2.trans_le (side _ member.2))
  · intro x member
    exact sub_nonpos.mpr (opposite x member)

end Unfoldings.FacewiseDevelopment
