module

public import Unfoldings.Roof.CompatibleCutCarrier
public import Unfoldings.Geometry.PolygonalRayGerm

/-! The actual compatible one-ended cut forest is closed, including all terminal rays. -/

@[expose] public section

open Topology

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- No finite outer truncation is needed for closedness of the original cut carrier. -/
theorem isClosed_carrier : IsClosed R.carrier := by
  apply IsClosed.union
  · apply isClosed_iUnion_of_finite
    intro e
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  · apply isClosed_iUnion_of_finite
    intro r
    let index := R.terminalIndex r
    have nonzero : R.exterior.direction (R.exterior.slope index) ≠ 0 := by
      intro zero
      have unit := R.exterior.unit index
      rw [zero, norm_zero] at unit
      exact zero_ne_one unit
    have line : IsClosedEmbedding (fun t : ℝ => R.exterior.ray index t) :=
      (Homeomorph.addLeft (R.exterior.point index)).isClosedEmbedding.comp
        (isClosedEmbedding_smul_left nonzero)
    have equality : {x | ∃ t : ℝ, 0 ≤ t ∧ x = R.exterior.ray index t} =
        (fun t : ℝ => R.exterior.ray index t) '' Set.Ici 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Ici, eq_comm]
    rw [equality]
    exact line.isClosedMap _ isClosed_Ici

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
