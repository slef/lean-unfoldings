module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionBankChainPositions
public import Unfoldings.Cap.CompletedRadiusPrefix
public import Unfoldings.Cap.SectorSweepBall
public import Unfoldings.Cap.ProperComparisonData
public import Unfoldings.Cap.CompletedProperComparisonData

/-! Actual roof face bounds construct proper comparison arcs in any specified bank calibration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}

/-- Apply the actual physical prefix construction in this same calibration.
The start is a specified contour copy, not a different copy of the same vertex. -/
theorem completionOutward_proper_comparison_data (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (T.supportPlanes i).normal 2) (cutoff : ℝ)
    (deep : Metric.closedBall origin cutoff ⊆ interior (T.domain))
    (μ : ℝ) (nonnegative : 0 ≤ μ) :
    let inside := M.inside
    let F := T.cornerTails inside
    let L := T.radialMesh M.inside
    let Q := L.cap
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let R := (M.completionOutwardForest T positive small).val
    ∀ (D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain)
      (B : R.FiveSectorFrameData positive small (R.completedDevelopment D)),
      (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
        p - origin ∈ closedFiveSector t i →
        p ∈ sectorSweepInterior positive small origin cutoff →
        μ * ‖p - origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q origin)).re ∧
        μ * ‖p - origin‖ ≤
          (B.sectorFrame i (D.projectedPlacement Q f p -
            D.projectedMap Q origin)).im) →
      L.mesh.toTriangulation.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi →
      ∀ radius : ℝ, 2 * radius < cutoff →
      ∀ w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
        Q.projectedVertex w ∈ M.extendedGeometricCuts F →
        ‖Q.projectedVertex w - origin‖ < radius →
      ∀ target : Fin (R.completedContour.length + 1),
        L.mesh.toTriangulation.pairedComplex.vertexForgetCuts (Set.subset_univ _)
          (L.mesh.toTriangulation.pairedComplex.boundaryEndVertex R.completedRetain
            (R.completedContour.cycle.point target)) = w →
      ∀ circle : ℝ,
        ‖(R.completedDevelopment D).boundaryPosition (R.completedContour.cycle.point target) -
          D.projectedMap Q origin‖ < circle →
        circle < μ * radius →
        Nonempty (B.ProperComparisonData w target
          (D.projectedMap Q origin) radius circle) := by
  let inside := M.inside
  let F := T.cornerTails inside
  let L := T.radialMesh M.inside
  let Q := L.cap
  let := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
  let network := M.completionOutwardForest T positive small
  let R := network.val
  refine fun D B face_bounds budget => ?_
  intro radius room w member start target original circle near far
  obtain ⟨i, sectors, positions⟩ := M.completionOutward_bankChain_sector_positions
    positive small T height w member
  have radius_positive : 0 < radius := (norm_nonneg _).trans_lt start
  have radius_cutoff : radius ≤ cutoff := by linarith
  have deepQ : Metric.closedBall origin radius ⊆ interior Q.footprint := by
    rw [L.cap_footprint]
    exact (Metric.closedBall_subset_closedBall radius_cutoff).trans deep
  have bounded_faces (f) (p : Plane) (at_face : p ∈ (Q.projectedTriangle f).carrier)
      (bounded : ‖p - origin‖ ≤ radius)
      (cone : p - origin ∈ closedFiveSector t i) :=
    face_bounds i f p at_face cone (closedBall_subset_sectorSweepInterior positive small
      origin room
      (by change dist p origin ≤ radius; rw [dist_eq_norm]; exact bounded))
  obtain ⟨comparison, _⟩ := B.exists_proper_comparison_data_in_sector i network.property w member
    (D.projectedMap Q origin) μ radius nonnegative start deepQ positions
    (fun j => (sectors j).1) (fun j => (sectors j).2) bounded_faces budget target original
    circle near far
  exact ⟨comparison⟩

end Unfoldings.ConvexRoof.SectorForest
