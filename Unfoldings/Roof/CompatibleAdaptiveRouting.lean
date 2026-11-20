module

public import Unfoldings.Roof.AdaptivePotentialForest
public import Unfoldings.Roof.SelectedStrictRegion
public import Unfoldings.Convex.AdaptiveExteriorProgress
public import Unfoldings.Convex.ExteriorPieces
public import Unfoldings.Topology.AttachAscendingParents

/-! Combine adaptive original-edge histories with consistent outward rays
of the clipped extension. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

structure CompatibleAdaptiveRouting (U : Set Face) (G : SlopeEnvelope)
    (boundary : (frontier G.slopes).Nonempty) (L : Set Plane) (r margin η : ℝ) where
  original : K.AdaptivePotentialRouting U (G.boundaryEnvelope boundary) L r margin
  exterior : G.ExteriorPlan {v // v ∈ original.parents.roots}
  exterior_points : ∀ v, exterior.point v = K.projectedVertex v.val
  exterior_height : ∀ v : {v // v ∈ original.parents.roots},
    G.height (K.projectedVertex v.val) =
      (G.boundaryEnvelope boundary).height (K.projectedVertex v.val)
  within : L ⊆ G.slopes
  exterior_polar : ∀ v z, z ∈ SlopeEnvelope.historyCone L (exterior.slope v) →
    η * ‖z‖ ≤ inner ℝ z (exterior.direction (exterior.slope v))

open Classical in
/-- Construct both sets of parents using the adaptive headings in the interior
and the supplied, consistently assigned supporting direction at each boundary slope. -/
theorem exists_compatibleAdaptiveRouting {slopes : Set Plane} (convex : Convex ℝ slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (L : Set Plane) (within : L ⊆ slopes)
    {r θ maxWidth η : ℝ} (r_positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    (nonnegative : 0 ≤ θ) (acute : (maxWidth + θ) / 2 < Real.pi / 2)
    (angles : ∀ f, K.normalSlope f ∈ slopes → ∀ i, (K.projectedTriangle f).cornerAngle i ≤ θ)
    (cones : ∀ p ∈ frontier slopes, ∃ (axis : Plane) (width : ℝ),
      axis ≠ 0 ∧ θ ≤ width ∧ width ≤ maxWidth ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2))
    (direction : Plane → Plane)
    (outward : ∀ p ∈ frontier slopes, ‖direction p‖ = 1 ∧ 0 < inner ℝ (direction p) p ∧
      ∀ w ∈ slopes, inner ℝ (direction p) w ≤ inner ℝ (direction p) p)
    (polar : ∀ p ∈ frontier slopes, ∀ z ∈ SlopeEnvelope.historyCone L p,
      η * ‖z‖ ≤ inner ℝ z (direction p)) :
    Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary L r (Real.cos ((maxWidth + θ) / 2)) η) := by
  let G := K.clippedExtension slopes compact nonempty
  let B := G.boundaryEnvelope boundary
  let U : Set Face := {f | K.normalSlope f ∈ slopes}
  obtain ⟨I⟩ := K.exists_adaptivePotentialRouting U B L r_positive disk nonnegative acute angles cones
  let V := {v // v ∈ I.parents.roots}
  let point (v : V) := K.projectedVertex v.val
  have strict_iff (x : Plane) :
      B.height x < G.height x ↔ x ∈ interior (K.selectedCarrier slopes) :=
    (K.clippedExtension_strict_region_iff compact nonempty boundary x).trans
      (K.interior_selectedCarrier_iff_normal_cell convex compact no_boundary x).symm
  have equal (v : V) : G.height (point v) = B.height (point v) := by
    have outside : point v ∉ interior (K.selectedCarrier slopes) :=
      (Set.ext_iff.mp I.roots_eq v.val).mp v.property
    exact le_antisymm (le_of_not_gt (fun strict => outside ((strict_iff _).mp strict)))
      (G.boundary_height_le boundary _)
  choose p hp using fun v : V => B.exists_active (point v)
  let exterior : G.ExteriorPlan V := {
    point := point
    point_injective := K.projectedVertex_injective.comp Subtype.val_injective
    slope := p
    direction := direction
    active v := ⟨compact.isClosed.frontier_subset (hp v).1, (equal v).trans (hp v).2⟩
    unit v := (outward (p v) (hp v).1).1
    positive v := (outward (p v) (hp v).1).2.1
    support v := (outward (p v) (hp v).1).2.2 }
  exact ⟨⟨I, exterior, fun _ => rfl, equal, within, fun v => polar (p v) (hp v).1⟩⟩

namespace CompatibleAdaptiveRouting

variable {K} {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {L : Set Plane} {r margin η : ℝ} (R : K.CompatibleAdaptiveRouting U G boundary L r margin η)

theorem shared_height (v : {v // v ∈ R.original.parents.roots}) :
    R.exterior.parents.height v = R.original.parents.height v.val := by
  change G.height (R.exterior.point v) = R.original.parents.height v.val
  rw [R.exterior_points, R.original.height_eq]
  exact R.exterior_height v

/-- The complete finite parent forest keeps original interior links and
ends at the roots with no further ray contact. -/
def parents : AscendingParents (C.Vertex Set.univ) :=
  R.original.parents.attach R.exterior.parents R.shared_height

theorem rootedForest : R.parents.graph.IsRootedForest R.parents.roots :=
  R.parents.graph_rootedForest

/-- All oriented partial interior links and exterior ray segments. This
includes truncated contact links and arbitrary pieces of terminal tails. -/
def FollowsStep (x y : Plane) : Prop :=
  (∃ v : {v // v ∉ R.original.parents.roots}, ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
    let start := K.projectedVertex v.val
    let d := K.projectedVertex (R.original.parents.parent v.val) - start
    x = start + s • d ∧ y = start + t • d) ∨
  (∃ v : {v // v ∈ R.original.parents.roots}, ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧
    x = R.exterior.ray v s ∧ y = R.exterior.ray v t)

theorem followsStep_progress {x y : Plane} (step : R.FollowsStep x y) :
    (G.boundaryEnvelope boundary).HistoryProgress L x y := by
  rcases step with ⟨v, s, t, start, ordered, _, rfl, rfl⟩ | ⟨v, s, t, start, ordered, rfl, rfl⟩
  · exact R.original.along v.val v.property s t start ordered
  · exact R.exterior.historyProgress_ray boundary R.within v start ordered

/-- Every complete sequence of partial adaptive links has the same length-to-chord
bound as its individual original and exterior histories. -/
theorem follows_length_bound (r_positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
    {b : ℝ} (upper : ∀ p ∈ G.slopes, ‖p‖ ≤ b)
    {n : ℕ} (P : PolygonalChain Plane n)
    (follows : ∀ i : Fin n, R.FollowsStep (P.vertex i.castSucc) (P.vertex i.succ)) :
    P.projectedLength ≤ (b / r) * ‖P.vertex (Fin.last n) - P.vertex 0‖ :=
  (G.boundaryEnvelope boundary).historyProgress_chain_length r_positive disk
    (fun p hp => upper p (G.compact.isClosed.frontier_subset hp)) P
    (fun i => R.followsStep_progress (follows i))

end CompatibleAdaptiveRouting
end Unfoldings.ConvexRoof
