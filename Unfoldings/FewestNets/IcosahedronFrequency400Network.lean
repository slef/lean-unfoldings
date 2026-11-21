module

public import Unfoldings.FewestNets.IcosahedronNetworkFromStars
public import Unfoldings.FewestNets.FiniteMeshCorner400Bounds
public import Unfoldings.FewestNets.IcosahedronNetworkPerimeter
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Bounds

/-! The frequency-400 icosahedral mesh is a separated spherical Voronoi network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real

/-- All network geometry hypotheses for the second endpoint mesh. -/
theorem voronoiNetwork_q400 :
    VoronoiNetwork (fun a : meshSites 400 => (a : Space))
      (meshEndpoint (by decide : 0 < (400 : ℕ))) (icosahedronEdge / 2200) (108 * π / 180) := by
  let o := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have edgepos : 0 < icosahedronEdge := by unfold icosahedronEdge; positivity
  have edgele : icosahedronEdge ≤ 2 := by
    unfold icosahedronEdge
    rw [div_le_iff₀ (by positivity)]
    have root : (2 : ℝ) ≤ √(10 + 2 * √5) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith [Real.sqrt_nonneg 5])
    linarith only [root]
  apply voronoiNetwork_of_corner_bounds (by decide : 100 ≤ 400) (by decide) o
  · positivity
  · norm_num
    linarith only [edgepos]
  · linarith only [edgele]
  · linarith only [edgele, Real.pi_gt_three]
  · positivity
  · linarith only [Real.pi_pos]
  · exact meshCornerBounds_of_canonical_stars (by decide : 100 ≤ 400) (by decide) o
      (by positivity) (by linarith only [Real.pi_pos])
      (fun _ _ key => q400_face_corner_bounds key)
      (fun _ key => q400_seam_corner_bounds key)
      q400_pentagon_corner_bounds

/-- The actual frequency-400 dual arc length satisfies the second perimeter bound. -/
theorem networkLength_q400_lt [Fintype (MeshEdge 400)] :
    networkLength (meshEndpoint (by decide : 0 < (400 : ℕ))) < 8336 := by
  apply lt_of_le_of_lt (networkLength_le_weightedArcUpperTotal (by decide : 100 ≤ 400)
    (by decide) (fun _ _ key k => (q400_face_corner_bounds key k).1)
    (fun _ key k => (q400_seam_corner_bounds key k).1)
    (fun k => (q400_pentagon_corner_bounds k).1))
  exact weightedArcUpperTotal_q400

end Unfoldings.FewestNets.Icosahedron
