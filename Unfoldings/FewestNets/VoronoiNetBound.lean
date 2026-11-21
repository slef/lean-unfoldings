module

public import Unfoldings.FewestNets.VoronoiComponentCount

/-! Assemble original-edge nets after the geometric rotation count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {I J : Type*} [Finite I] [Nonempty I] [Fintype J]
  {site : I → Space} {endpoint : J → Bool → Space}

include P in
/-- Once each admissible normal component has a net, the rotation estimate
bounds the number of pieces by the stated coefficient at the input corner limit. -/
theorem exists_netPartition_lt_of_voronoi_network {separation psi θ limit : ℝ}
    (H : VoronoiNetwork site endpoint separation psi)
    (acute : θ < π / 2) (corners : ∀ f i, (C.triangle f).cornerAngle i ≤ θ)
    (numeric : 2 + componentCoefficient (Fintype.card J) (networkLength endpoint)
      separation psi / cos θ < limit)
    (nets : ∀ g : SpatialRotation,
      (∀ f, N.normal f ∈ strictVoronoiCone (fun j => linear g (site j))
        (voronoiLabel site (N.normal f) g)) →
      ∀ c : (C.labeledSeamGraph (fun f => voronoiLabel site (N.normal f) g)).ConnectedComponent,
        C.HasOriginalEdgeNet c.supp) :
    ∃ n : ℕ, (n : ℝ) < limit ∧ C.HasNetPartition n := by
  let η := π - 2 * θ
  have positive : 0 < η := by dsimp [η]; linarith
  have minimum (f : Face) (i : Fin 3) : η ≤ (C.triangle f).cornerAngle i :=
    cornerAngle_lower_of_upper (C.triangle f) θ (corners f) i
  obtain ⟨g, good, count, _⟩ :=
    P.exists_rotation_with_bounded_voronoi_components N H positive minimum
  have sine : sin (η / 2) = cos θ := by
    rw [show η / 2 = π / 2 - θ by dsimp [η]; ring, sin_pi_div_two_sub]
  rw [sine] at count
  exact ⟨_, count.trans_lt numeric, C.hasNetPartition_card_labeledSeamGraph _ (nets g good)⟩

end Unfoldings.SpatialFolding.ConvexBoundary
