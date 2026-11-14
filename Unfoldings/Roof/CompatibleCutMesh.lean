module

public import Unfoldings.Roof.TruncatedCutSegments
public import Unfoldings.Roof.SpatialEnvelopeInteriorSeams

/-! Construct a conforming physical mesh respecting every bounded compatible cut segment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)

/-- All original triangle lines, together with each cut's supporting and endpoint lines. -/
def compatibleCutEquations :
    ((Fin (Fintype.card Face) × Fin 3) ⊕
      (Fin (Fintype.card (C.Vertex Set.univ)) × Fin 3)) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord i.2)
    (segmentEquations (R.cutFirst level) (R.cutLast level higher)
      (K.cut_endpoints_ne compact nonempty R no_boundary level higher))

theorem compatibleCutEquations_ne_zero
    (i : (Fin (Fintype.card Face) × Fin 3) ⊕
      (Fin (Fintype.card (C.Vertex Set.univ)) × Fin 3)) :
    K.compatibleCutEquations compact nonempty R no_boundary level higher i ≠ 0 := by
  cases i with
  | inl i => exact (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord_ne_zero i.2
  | inr i =>
    exact segmentEquations_ne_zero (R.cutFirst level) (R.cutLast level higher)
      (K.cut_endpoints_ne compact nonempty R no_boundary level higher) i

/-- An actual finite conforming physical roof mesh at the chosen level. -/
def compatibleCutMesh : SpatialEnvelope.ConstrainedTriangulation M.plane
    (K.compatibleCutEquations compact nonempty R no_boundary level higher) (-level) :=
  M.mesh _ (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher)
    positive inner_disk (q := R.cutInteriorPoint)
    (by have bound := R.cutInteriorPoint_height level higher; linarith)

local instance compatibleMeshIndexFintype : Fintype
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk).Index :=
  @Fintype.ofFinite _
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk).finite

theorem compatibleCutMesh_conforming : TriangleFamily.Conforming
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk
      ).projectedTriangle :=
  M.mesh_conforming _
    (K.compatibleCutEquations_ne_zero compact nonempty R no_boundary level higher)
    positive inner_disk (q := R.cutInteriorPoint) _

include R higher in
theorem compatible_section_interior :
    (interior (SpatialEnvelope.clip M.plane (-level))).Nonempty := by
  rw [M.clip_eq_sublevel, neg_neg]
  exact ⟨R.cutInteriorPoint,
    (K.clippedExtension slopes compact nonempty).mem_interior_sublevel
      (R.cutInteriorPoint_height level higher)⟩

theorem compatibleCutMesh_segment_cover (i : Fin (Fintype.card (C.Vertex Set.univ))) :
    let T := K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk
    segment ℝ (R.cutFirst level i) (R.cutLast level higher i) =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆
          segment ℝ (R.cutFirst level i) (R.cutLast level higher i)},
        (T.projectedTriangle e.val.1).edge e.val.2 := by
  let T := K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk
  let S : SpatialEnvelope.ConstrainedTriangulation M.plane
      (segmentEquations (R.cutFirst level) (R.cutLast level higher)
        (K.cut_endpoints_ne compact nonempty R no_boundary level higher)) (-level) := {
    toTriangulation := T.toTriangulation
    signs j k := T.signs j (.inr k)
    constrained j p member k := T.constrained j p member (.inr k) }
  apply S.prescribed_segment_eq_union_subedges
  · rw [M.clip_eq_sublevel, neg_neg]
    exact (R.cutFirst_height level higher i).le
  · rw [M.clip_eq_sublevel, neg_neg]
    exact R.cutLast_height level higher i

theorem compatibleCutMesh_cut_seam {p : Plane} (member : p ∈ R.truncatedCarrier level higher)
    (inside : p ∈ interior (SpatialEnvelope.clip M.plane (-level))) :
    let T := K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk
    ∃ s : T.pairedComplex.Seam, s ∉ T.toTriangulation.retainOutside
      (R.truncatedCarrier level higher) ∧
        p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
          (T.pairedComplex.left s).edge := by
  let T := K.compatibleCutMesh compact nonempty R no_boundary level higher M positive inner_disk
  let := T.finite
  let := Fintype.ofFinite T.Index
  rw [R.truncatedCarrier_eq_segments level higher] at member
  obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp member
  have cover := K.compatibleCutMesh_segment_cover compact nonempty R no_boundary level higher
    M positive inner_disk i
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (cover.subset on_segment)
  have selected : (T.projectedTriangle e.val.1).edge e.val.2 ⊆ R.truncatedCarrier level higher := by
    intro x hx
    rw [R.truncatedCarrier_eq_segments level higher]
    exact Set.mem_iUnion.mpr ⟨i, e.property hx⟩
  obtain ⟨s, cut, incident⟩ := T.toTriangulation.exists_cut_seam_of_projected_edge
    (K.compatibleCutMesh_conforming compact nonempty R no_boundary level higher
      M positive inner_disk)
    (K.compatible_section_interior compact nonempty R level higher M)
    (R.truncatedCarrier level higher) ⟨e.val.1, e.val.2⟩ selected on_edge inside
  refine ⟨s, cut, ?_⟩
  rcases incident with first | last
  · change (⟨e.val.1, e.val.2⟩ : EdgeRef T.Index) = T.pairedComplex.left s at first
    change p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
      (T.pairedComplex.left s).edge
    rw [← first]
    exact on_edge
  · change (⟨e.val.1, e.val.2⟩ : EdgeRef T.Index) = T.pairedComplex.right s at last
    change p ∈ (T.projectedTriangle (T.pairedComplex.left s).face).edge
      (T.pairedComplex.left s).edge
    rw [T.toTriangulation.paired_seam_projected_edge, ← last]
    exact on_edge

end Unfoldings.ConvexRoof
