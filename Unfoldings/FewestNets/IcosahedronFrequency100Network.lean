module

public import Unfoldings.FewestNets.IcosahedronNetworkFromStars
public import Unfoldings.FewestNets.FiniteMeshCorner100Bounds

/-! The frequency-100 icosahedral mesh is a separated spherical Voronoi network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real

/-- All network geometry hypotheses for the first endpoint mesh. -/
theorem voronoiNetwork_q100 :
    VoronoiNetwork (fun a : meshSites 100 => (a : Space))
      (meshEndpoint (by decide : 0 < (100 : ℕ))) (icosahedronEdge / 700) (107 * π / 180) := by
  let o := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have edgepos : 0 < icosahedronEdge := by unfold icosahedronEdge; positivity
  have edgele : icosahedronEdge ≤ 2 := by
    unfold icosahedronEdge
    rw [div_le_iff₀ (by positivity)]
    have root : (2 : ℝ) ≤ √(10 + 2 * √5) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith [Real.sqrt_nonneg 5])
    linarith only [root]
  apply voronoiNetwork_of_corner_bounds (by decide : 100 ≤ 100) (by decide) o
  · positivity
  · norm_num
    linarith only [edgepos]
  · linarith only [edgele]
  · linarith only [edgele, Real.pi_gt_three]
  · positivity
  · linarith only [Real.pi_pos]
  · exact meshCornerBounds_of_canonical_stars (by decide : 100 ≤ 100) (by decide) o
      (by positivity) (by linarith only [Real.pi_pos])
      (fun _ _ key => q100_face_corner_bounds key)
      (fun _ key => q100_seam_corner_bounds key)
      q100_pentagon_corner_bounds

end Unfoldings.FewestNets.Icosahedron
