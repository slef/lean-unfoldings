module

public import Unfoldings.Roof.AffineFloorSharpHeading
public import Unfoldings.Geometry.DirectionFrame
public import Unfoldings.Geometry.PlanarConjugation

/-! A forward direction gives an actual bank chart, reflected if its positive face lies below. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedBoundaryChain_edge_reorient (E : Plane ≃ₗᵢ[ℝ] Plane)
    {retain : Set C.Seam} {n : ℕ} (bank : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    ((K.reorient E).folding.projectedBoundaryChain bank).edge i =
      E ((K.folding.projectedBoundaryChain bank).edge i) := by
  simp only [PolygonalChain.edge, K.projectedBoundaryChain_start_germ,
    K.projectedBoundaryChain_finish_germ, (K.reorient E).projectedBoundaryChain_start_germ,
    (K.reorient E).projectedBoundaryChain_finish_germ, map_sub]
  exact congrArg₂ (· - ·)
    (K.projectFace_reorient E _ ((C.triangle _).vertex (C.germFarCorner (bank.point i).val).2))
    (K.projectFace_reorient E _ ((C.triangle _).vertex (bank.point i).val.1.2))

theorem projectedGermOrientation_reflect_chart (E : Plane ≃ₗᵢ[ℝ] Plane) (p : C.Germ) :
    (K.reorient (E.trans planeConjugation)).projectedGermOrientation p =
      -(K.reorient E).projectedGermOrientation p := by
  simp [projectedGermOrientation, K.projectFace_reorient, LinearIsometryEquiv.trans_apply,
    planeConjugation_apply, orient]
  ring

/-- One orthogonal chart follows the given direction forward and places
the named original bank's incident faces above it. -/
theorem exists_forwardBankChart {retain : Set C.Seam} {n : ℕ}
    (bank : (C.boundarySystem retain).Chain n) (axis : Plane) (unit : ‖axis‖ = 1)
    (progress : ∀ i, 0 < inner ℝ axis ((K.folding.projectedBoundaryChain bank).edge i)) :
    ∃ E : Plane ≃ₗᵢ[ℝ] Plane,
      (∀ i, 0 < ((K.reorient E).folding.projectedBoundaryChain bank).edge i 0) ∧
        0 < (K.reorient E).projectedGermOrientation bank.first.val := by
  let E := directionFrame axis
  have coord (p : Plane) : E p 0 = inner ℝ axis p := by
    rw [← E.inner_map_map]
    change E p 0 = inner ℝ (directionFrame axis axis) (E p)
    rw [directionFrame_apply, unit, EuclideanSpace.inner_single_left]
    simp
  have forward (i : Fin (n + 1)) :
      0 < ((K.reorient E).folding.projectedBoundaryChain bank).edge i 0 := by
    rw [K.projectedBoundaryChain_edge_reorient, coord]
    exact progress i
  by_cases sign : 0 < (K.reorient E).projectedGermOrientation bank.first.val
  · exact ⟨E, forward, sign⟩
  refine ⟨E.trans planeConjugation, ?_, ?_⟩
  · intro i
    rw [K.projectedBoundaryChain_edge_reorient]
    change 0 < planeConjugation (E ((K.folding.projectedBoundaryChain bank).edge i)) 0
    rw [planeConjugation_apply]
    change 0 < E ((K.folding.projectedBoundaryChain bank).edge i) 0
    rw [coord]
    exact progress i
  · rw [K.projectedGermOrientation_reflect_chart]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt sign)
      ((K.reorient E).projectedGermOrientation_ne_zero _))

end Unfoldings.ConvexRoof
