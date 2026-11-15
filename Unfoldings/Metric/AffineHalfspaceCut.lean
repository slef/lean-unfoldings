module

public import Unfoldings.Metric.PolygonalBoundaryCuts
public import Unfoldings.Geometry.AffineSideRayCells
public import Unfoldings.Geometry.AffineSupportBoundary

/-! The intrinsic cells on one side of an affine cut form the exact full closed halfspace. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
  (f : E →ᵃ[ℝ] ℝ) (signs : I → Bool)

include closed in
/-- All cells of one specified side cover its closed halfspace, including every bank point. -/
theorem affineHalfspace_eq_iUnion (cover : (⋃ i, cells i) = Set.univ)
    (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
    (side : Bool) (positive : ∃ q, 0 < AffineArrangement.signed f side q) :
    {x | 0 ≤ AffineArrangement.signed f side x} =
      ⋃ i : {i // signs i = side}, cells i.val := by
  ext x
  constructor
  · exact AffineArrangement.mem_iUnion_cells_on_side cells closed cover f signs aligned
      side positive
  · intro member
    obtain ⟨i, inside⟩ := Set.mem_iUnion.mp member
    change 0 ≤ AffineArrangement.signed f side x
    simpa only [i.property] using aligned i.val x inside

/-- One-sided physical seam gluing is the complete intrinsic halfspace even when its
boundary is cut. The actual finite partition supplies every boundary identification. -/
def affineHalfspaceCutIsometryEquiv (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : (⋃ i, cells i) = Set.univ)
    (proper : f ≠ 0)
    (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
    (side : Bool) (positive : ∃ q, 0 < AffineArrangement.signed f side q)
    (cuts : Set E) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0) :
    PolygonalCut (fun i : {i // signs i = side} => cells i.val) (fun i => closed i.val) cuts ≃ᵢ
      PolygonalPoint {x | 0 ≤ AffineArrangement.signed f side x} := by
  apply boundaryCutIsometryEquiv (fun i : {i // signs i = side} => cells i.val)
    (fun i => closed i.val) cuts (fun i => convex i.val) (fun i => full i.val)
    (affineHalfspace_eq_iUnion cells closed f signs cover aligned side positive)
    ((convex_Ici (0 : ℝ)).affine_preimage _) cut_closed
  apply Set.disjoint_left.mpr
  intro x inside on_cut
  have zero : AffineArrangement.signed f side x = 0 := by
    simp only [AffineArrangement.signed_apply, cut_level x on_cut, neg_zero, ite_self]
  have nonzero : AffineArrangement.signed f side ≠ 0 := by
    cases side <;> simpa only [AffineArrangement.signed, Bool.false_eq_true, ↓reduceIte,
      neg_ne_zero] using proper
  exact not_mem_interior_of_affine_lower_bound (AffineArrangement.signed f side)
    nonzero (fun _ hx => hx) zero inside

end Unfoldings.MetricGluing
