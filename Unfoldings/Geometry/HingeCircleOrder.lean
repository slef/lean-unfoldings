module

public import Unfoldings.Geometry.HingeCircleAsymptote
public import Unfoldings.Topology.NoncrossingOrder

/-! Positive hinge openings move actual circle contacts counterclockwise about the source. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (outward : (R.suffix hinge).Outward) (positive : 0 < angle) (small : angle < Real.pi)

include outward small radial in
/-- The actual positive angular displacement increases with the opening angle at every source
radius beyond the hinge. Orientation is proved from terminal-ray limits and noncontact. -/
theorem strictMono_hingeCircleAngle
    (r : Set.Ioi (nndist R.start (R.chain.vertex hinge))) :
    StrictMono (fun θ => R.hingeCircleAngle hinge nonzero angle radial positive (θ, r)) := by
  let : PreconnectedSpace (Set.Ioi (nndist R.start (R.chain.vertex hinge))) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  intro θ ψ before
  have first : Continuous (fun s : Set.Ioi (nndist R.start (R.chain.vertex hinge)) =>
      R.hingeCircleAngle hinge nonzero angle radial positive (θ, s)) :=
    (R.continuous_hingeCircleAngle hinge nonzero angle radial outward positive small).comp
      (continuous_const.prodMk continuous_id)
  have last : Continuous (fun s : Set.Ioi (nndist R.start (R.chain.vertex hinge)) =>
      R.hingeCircleAngle hinge nonzero angle radial positive (ψ, s)) :=
    (R.continuous_hingeCircleAngle hinge nonzero angle radial outward positive small).comp
      (continuous_const.prodMk continuous_id)
  exact lt_of_continuous_noncontact_of_tendsto first last
    (fun s equal => before.ne (R.hingeCircleAngle_injective hinge nonzero angle radial outward
      positive small s equal))
    (R.tendsto_hingeCircleAngle hinge nonzero angle radial positive small θ)
    (R.tendsto_hingeCircleAngle hinge nonzero angle radial positive small ψ) before r

end Unfoldings.PolygonalRay
