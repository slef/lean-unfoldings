module

public import Unfoldings.Roof.CompletionLeafCoherence
public import Unfoldings.Roof.GeometricSectorData
public import Unfoldings.Geometry.RecoverableStripRegularWidth
public import Unfoldings.Cap.ClosedSectorStrip

/-! Positive-height regular points avoid every actual geometric waterfall pinch. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (T : K.CompletionMesh φ region extra)

theorem regular_meshed_point_ne_geometric_vertex (positive : 0 < t) (small : t < 1) :
    let F := T.cornerTails M.inside
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ p ∈ interior
      (SpatialEnvelope.clip (K.completionPlanes T.tentHeight (Real.sin φ / 2)) T.level),
      (∀ f j, p ≠ (L.cap.projectedTriangle f).vertex j) →
      ∀ w : F.GeometricVertex, p ≠ F.geometricPosition w := by
  let F := T.cornerTails M.inside
  let covered := T.cornerTails_covers_rim M.inside
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  refine fun p inside regular w same => ?_
  by_cases root : w ∈ (M.geometricParents F covered positive small).roots
  · obtain ⟨c, rfl⟩ := root
    change p = (F.componentTail c).tip at same
    exact (F.componentTail c).boundary.2 (same ▸ inside)
  · obtain ⟨v, position, _⟩ := M.meshed_geometric_nonroot_vertex T positive small w root
    change L.cap.projectedVertex v = F.geometricPosition w at position
    obtain ⟨⟨f, j⟩, rfl⟩ :=
      L.mesh.toTriangulation.pairedComplex.vertexOfCorner_surjective Set.univ v
    exact regular f j (same.trans position.symm)

theorem regular_point_not_waterfall_pinches (positive : 0 < t) (small : t < 1) (i : FiveSector) :
    let F := T.cornerTails M.inside
    let covered := T.cornerTails_covers_rim M.inside
    let B := fiveSectorFrame t positive small i
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ z : ℂ, origin + B.place.symm z ∈ interior
      (SpatialEnvelope.clip (K.completionPlanes T.tentHeight (Real.sin φ / 2)) T.level) →
      0 < z.re + z.im →
      (∀ f j, origin + B.place.symm z ≠ (L.cap.projectedTriangle f).vertex j) →
      z ∉ insert 0 (Set.range (fun leaf : M.GeometricSectorLeaf F covered positive small i =>
        leaf.point)) := by
  let F := T.cornerTails M.inside
  let covered := T.cornerTails_covers_rim M.inside
  let B := fiveSectorFrame t positive small i
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  refine fun z inside after_source regular member => ?_
  have avoid := M.regular_meshed_point_ne_geometric_vertex T positive small
    (origin + B.place.symm z) inside regular
  rcases member with source | leaf
  · simp only [source, Complex.zero_re, Complex.zero_im, add_zero,
      lt_self_iff_false] at after_source
  · obtain ⟨leaf, rfl⟩ := leaf
    apply avoid leaf.val
    change origin + B.place.symm (B.place (F.geometricPosition leaf.val - origin)) = _
    rw [B.place.symm_apply_apply]
    abel

theorem regular_waterfall_bank_width (positive : 0 < t) (small : t < 1) (i : FiveSector)
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (S : MonotoneStrip) (cell : S ∈ P.cells) (cutoff : ℝ)
    (deep : Metric.closedBall origin cutoff ⊆ interior
      (SpatialEnvelope.clip (K.completionPlanes T.tentHeight (Real.sin φ / 2)) T.level))
    (pinches : S.RecoverablePinchesIn
      (insert 0 (Set.range (fun leaf : M.GeometricSectorLeaf (T.cornerTails M.inside)
        (T.cornerTails_covers_rim M.inside) positive small i => leaf.point))) 0 cutoff) :
    let B := fiveSectorFrame t positive small i
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∀ {z : ℂ}, z ∈ S.carrier → z.re + z.im ∈ Set.Icc 0 cutoff →
      0 < z.re + z.im →
      (∀ f j, origin + B.place.symm z ≠ (L.cap.projectedTriangle f).vertex j) →
      ∀ {k : ℝ}, k ∈ Set.Icc (z.re + z.im) cutoff →
        S.lower.coordinate k < S.upper.coordinate k →
        S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im) := by
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  refine fun {z} member slab after_source regular {k} active width => ?_
  have bounds := P.cell_bounds cell (z.re + z.im)
  have root : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier :=
    ⟨bounds.1.trans member.1, member.2.trans bounds.2⟩
  have physical := deep (closed_sector_strip_slab_mem_closedBall positive small i origin root slab)
  exact S.width_pos_of_recoverable_regular pinches member slab active width
    (M.regular_point_not_waterfall_pinches T positive small i z physical after_source regular)

end Unfoldings.ConvexRoof.SectorForest
