module

public import Unfoldings.Polyhedron.GaussianChartTurns
public import Unfoldings.Geometry.ConvexArcChordOrder

/-! The actual Gaussian chord cycle has one orientation in every orthonormal chart frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap

attribute [local instance] Complex.finrank_real_complex_fact

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

include P closes covers in
theorem gaussian_chart_chord_orientation
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    (q : Space) (center : q ∈ F.gaussianCell (F.gaussianSiteOfVertex a))
    (strict : q ∈ interior (F.gaussianCone (F.gaussianSiteOfVertex a)))
    (hemisphere : ∀ z ∈ F.gaussianCell (F.gaussianSiteOfVertex a), 0 < inner ℝ q z)
    (frame : Plane ≃ₗᵢ[ℝ] ℂ) :
    let p := frame ∘ stereographicCoord ∘ northFrame q ∘ compressedLinkNormal N c count
    (∀ i j, 0 ≤ chordSide p i (p j)) ∧
      (∀ i, 0 < chordSide p i (p (finRotate (m + 1) (finRotate (m + 1) i)))) ∨
    (∀ i j, chordSide p i (p j) ≤ 0) ∧
      (∀ i, chordSide p i (p (finRotate (m + 1) (finRotate (m + 1) i))) < 0) := by
  let base := compressedLinkNormal N c count
  let project := stereographicCoord ∘ northFrame q
  let arc (i : Fin (m + 1)) := project '' closedMinorArc (base i) (base (finRotate (m + 1) i))
  let K := F.gaussianChartRegion (F.gaussianSiteOfVertex a) q
  let p := frame ∘ project ∘ base
  let E (i : Fin (m + 1)) := frame '' arc i
  obtain ⟨pinj, sub, preconnected, arc_incidence⟩ :=
    P.compressedLinkNormal_chart_arcs N c closes covers count extreme q center strict hemisphere
  have three := P.three_le_count_compressedLinkNormal N c closes covers count extreme
  have closed : IsClosed K := (F.gaussianChartRegion_properties _ center hemisphere).1.isClosed
  have sc : StrictConvex ℝ K := F.strictConvex_gaussianChartRegion _ center strict
  have closed_image := frame.toHomeomorph.isClosedMap K closed
  have sc_image := sc.linear_image (frame.toLinearEquiv : Plane →ₗ[ℝ] ℂ)
    frame.toHomeomorph.isOpenMap
  have included (i : Fin (m + 1)) : E i ⊆ frontier (frame '' K) := by
    have image := frame.toHomeomorph.image_frontier K
    change frame '' frontier K = frontier (frame '' K) at image
    rw [← image]
    exact Set.image_mono (sub i)
  have incidence (i j : Fin (m + 1)) : p j ∈ E i ↔ j = i ∨ j = finRotate (m + 1) i := by
    change frame (project (base j)) ∈ frame '' arc i ↔ _
    rw [frame.injective.mem_set_image]
    exact arc_incidence i j
  exact convex_arc_chord_orientation p closed_image sc_image three
    (fun i => included i ((incidence i i).mpr (Or.inl rfl)))
    (frame.injective.comp pinj) E
    (fun i => (preconnected i).image frame frame.continuous.continuousOn) included incidence

end Unfoldings.SpatialFolding.ConvexBoundary
