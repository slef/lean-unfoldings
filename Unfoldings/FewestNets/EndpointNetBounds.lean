module

public import Unfoldings.FewestNets.VoronoiNetBound

/-! Instantiate the rotation bound with the two endpoint mesh budgets. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {I J : Type*} [Finite I] [Nonempty I] [Fintype J]
  {site : I → Space} {endpoint : J → Bool → Space}

private theorem coefficient_le_of_length_le {edges length bound separation psi : ℝ}
    (positive : 0 < separation) (h : length ≤ bound) :
    componentCoefficient edges length separation psi ≤
      componentCoefficient edges bound separation psi := by
  unfold componentCoefficient
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact max_le_max le_rfl (div_le_div_of_nonneg_right h (mul_nonneg pi_pos.le positive.le))

include P in
/-- The first endpoint follows from the frequency-100 network bounds and
the original-edge developments of its admissible components. -/
theorem exists_netPartition_lt_q100_of_network
    (H : VoronoiNetwork site endpoint (icosahedronEdge / 700) (107 * π / 180))
    (edges : Fintype.card J = 300000) (length : networkLength endpoint ≤ 2084)
    (corners : ∀ f i, (C.triangle f).cornerAngle i ≤ 81 * π / 180)
    (nets : ∀ g : SpatialRotation,
      (∀ f, N.normal f ∈ strictVoronoiCone (fun j => linear g (site j))
        (voronoiLabel site (N.normal f) g)) →
      ∀ c : (C.labeledSeamGraph (fun f => voronoiLabel site (N.normal f) g)).ConnectedComponent,
        C.HasOriginalEdgeNet c.supp) :
    ∃ n < 11300000, C.HasNetPartition n := by
  let theta := 81 * π / 180
  have acute : theta < π / 2 := by dsimp [theta]; linarith [pi_pos]
  have cosine : 0 < cos theta := cos_pos_of_mem_Ioo ⟨by dsimp [theta]; linarith [pi_pos], acute⟩
  have budget : componentCoefficient (Fintype.card J) (networkLength endpoint)
      (icosahedronEdge / 700) (107 * π / 180) ≤ 1767000 := by
    rw [edges, Nat.cast_ofNat]
    exact (coefficient_le_of_length_le H.separationPositive length).trans
      componentCoefficient_q100.le
  have numeric : 2 + componentCoefficient (Fintype.card J) (networkLength endpoint)
      (icosahedronEdge / 700) (107 * π / 180) / cos theta < (11300000 : ℝ) :=
    (add_le_add_right (div_le_div_of_nonneg_right budget cosine.le) 2).trans_lt endpoint_count_q100
  obtain ⟨n, less, net⟩ :=
    P.exists_netPartition_lt_of_voronoi_network N H acute corners numeric nets
  exact ⟨n, by exact_mod_cast less, net⟩

include P in
/-- The second endpoint follows from the frequency-400 network bounds and
the original-edge developments of its admissible components. -/
theorem exists_netPartition_lt_q400_of_network
    (H : VoronoiNetwork site endpoint (icosahedronEdge / 2200) (108 * π / 180))
    (edges : Fintype.card J = 4800000) (length : networkLength endpoint ≤ 8336)
    (corners : ∀ f i, (C.triangle f).cornerAngle i ≤ 83.2067 * π / 180)
    (nets : ∀ g : SpatialRotation,
      (∀ f, N.normal f ∈ strictVoronoiCone (fun j => linear g (site j))
        (voronoiLabel site (N.normal f) g)) →
      ∀ c : (C.labeledSeamGraph (fun f => voronoiLabel site (N.normal f) g)).ConnectedComponent,
        C.HasOriginalEdgeNet c.supp) :
    ∃ n < 200700000, C.HasNetPartition n := by
  let theta := 83.2067 * π / 180
  have acute : theta < π / 2 := by dsimp [theta]; linarith [pi_pos]
  have cosine : 0 < cos theta := cos_pos_of_mem_Ioo ⟨by dsimp [theta]; linarith [pi_pos], acute⟩
  have budget : componentCoefficient (Fintype.card J) (networkLength endpoint)
      (icosahedronEdge / 2200) (108 * π / 180) ≤ 23733000 := by
    rw [edges, Nat.cast_ofNat]
    exact (coefficient_le_of_length_le H.separationPositive length).trans
      componentCoefficient_q400.le
  have numeric : 2 + componentCoefficient (Fintype.card J) (networkLength endpoint)
      (icosahedronEdge / 2200) (108 * π / 180) / cos theta < (200700000 : ℝ) :=
    (add_le_add_right (div_le_div_of_nonneg_right budget cosine.le) 2).trans_lt endpoint_count_q400
  obtain ⟨n, less, net⟩ :=
    P.exists_netPartition_lt_of_voronoi_network N H acute corners numeric nets
  exact ⟨n, by exact_mod_cast less, net⟩

end Unfoldings.SpatialFolding.ConvexBoundary
