module

public import Unfoldings.Roof.TerminalTruncation

/-! A bounded embedded straight cut forest rooted exactly at its common level boundary. -/

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

include no_boundary higher in
theorem truncatedPoint_injective : Function.Injective (R.truncatedPoint level) := by
  intro x y equal
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (K.projectedVertex_injective equal)
    | inr y =>
      have same := congrArg (K.clippedExtension slopes compact nonempty).height equal
      have at_y := R.terminalPoint_level level higher y
      change (K.clippedExtension slopes compact nonempty).height (K.projectedVertex x) =
        (K.clippedExtension slopes compact nonempty).height (R.terminalPoint level y) at same
      rw [at_y] at same
      exact (ne_of_lt (higher x) same).elim
  | inr x =>
    cases y with
    | inl y =>
      have same := congrArg (K.clippedExtension slopes compact nonempty).height equal
      have at_x := R.terminalPoint_level level higher x
      change (K.clippedExtension slopes compact nonempty).height (R.terminalPoint level x) =
        (K.clippedExtension slopes compact nonempty).height (K.projectedVertex y) at same
      rw [at_x] at same
      exact (ne_of_lt (higher y) same.symm).elim
    | inr y =>
      by_cases same : x.val = y.val
      · exact congrArg Sum.inr (Subtype.ext same)
      · change R.terminalPoint level x = R.terminalPoint level y at equal
        exact (Set.disjoint_left.mp
          (K.compatible_openPieces_pairwise_disjoint compact nonempty R no_boundary same)
          (R.terminalPoint_mem_openPiece level higher x)
          (equal.symm ▸ R.terminalPoint_mem_openPiece level higher y)).elim

include no_boundary in
theorem truncated_segment_avoids_vertices
    (v : R.parents.LeafVertex) (nonroot : v ∉ (R.truncatedParents level higher).roots)
    (w : R.parents.LeafVertex) :
    R.truncatedPoint level w ∉ openSegment ℝ (R.truncatedPoint level v)
      (R.truncatedPoint level ((R.truncatedParents level higher).parent v)) := by
  cases v with
  | inr r => exact (nonroot ⟨r, rfl⟩).elim
  | inl v =>
    intro member
    cases w with
    | inl w =>
      exact K.compatible_openPiece_avoids_vertices compact nonempty R no_boundary v w
        (R.truncated_segment_subset_openPiece level higher v member)
    | inr w =>
      have strict := R.truncated_segment_height_lt level higher v member
      rw [R.truncatedPoint_level level higher w] at strict
      exact lt_irrefl _ strict

include no_boundary in
theorem truncated_segments_pairwise_disjoint :
    Pairwise (fun v w : {v // v ∉ (R.truncatedParents level higher).roots} =>
      Disjoint (openSegment ℝ (R.truncatedPoint level v.val)
        (R.truncatedPoint level ((R.truncatedParents level higher).parent v.val)))
        (openSegment ℝ (R.truncatedPoint level w.val)
          (R.truncatedPoint level ((R.truncatedParents level higher).parent w.val)))) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ different
  cases v with
  | inr r => exact (hv ⟨r, rfl⟩).elim
  | inl v =>
    cases w with
    | inr r => exact (hw ⟨r, rfl⟩).elim
    | inl w =>
      exact (K.compatible_openPieces_pairwise_disjoint compact nonempty R no_boundary
        (fun same => different (Subtype.ext (congrArg Sum.inl same)))).mono
          (R.truncated_segment_subset_openPiece level higher v)
          (R.truncated_segment_subset_openPiece level higher w)

/-- All old cut edges and truncated terminal rays, realized by their actual straight segments. -/
def truncatedCutEmbedding : FiniteEmbeddedGraph R.parents.LeafVertex
    {v // v ∉ (R.truncatedParents level higher).roots} Plane :=
  (R.truncatedParents level higher).segmentEmbedding (R.truncatedPoint level)
    (K.truncatedPoint_injective compact nonempty R no_boundary level higher)
    (K.truncated_segment_avoids_vertices compact nonempty R no_boundary level higher)
    (K.truncated_segments_pairwise_disjoint compact nonempty R no_boundary level higher)

theorem truncatedCutEmbedding_straight :
    (K.truncatedCutEmbedding compact nonempty R no_boundary level higher).IsStraight :=
  fun _ _ => rfl

theorem truncatedCutEmbedding_rootedForest :
    (K.truncatedCutEmbedding compact nonempty R no_boundary level higher).graph.IsRootedForest
      (Set.range Sum.inr) :=
  (R.truncatedParents level higher).segmentEmbedding_rootedForest (R.truncatedPoint level)
    (K.truncatedPoint_injective compact nonempty R no_boundary level higher)
    (K.truncated_segment_avoids_vertices compact nonempty R no_boundary level higher)
    (K.truncated_segments_pairwise_disjoint compact nonempty R no_boundary level higher)

theorem truncatedCutEmbedding_boundary_roots (v : R.parents.LeafVertex) :
    (K.truncatedCutEmbedding compact nonempty R no_boundary level higher).vertex v ∈
        frontier {x | (K.clippedExtension slopes compact nonempty).height x ≤ level} ↔
      v ∈ Set.range Sum.inr :=
  R.truncatedPoint_frontier_iff level higher v

theorem truncatedCutEmbedding_open_edges_interior
    (e : {v // v ∉ (R.truncatedParents level higher).roots})
    (t : unitInterval) (positive : 0 < t) (before : t < 1) :
    (K.truncatedCutEmbedding compact nonempty R no_boundary level higher).edge e t ∈
      interior {x | (K.clippedExtension slopes compact nonempty).height x ≤ level} := by
  obtain ⟨v, nonroot⟩ := e
  cases v with
  | inr r => exact (nonroot ⟨r, rfl⟩).elim
  | inl v =>
    apply (K.clippedExtension slopes compact nonempty).mem_interior_sublevel
    apply R.truncated_segment_height_lt level higher v
    rw [openSegment_eq_image_lineMap]
    exact ⟨t.val, ⟨positive, before⟩, rfl⟩

variable (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel) {Z : ℝ}
  (T : SpatialEnvelope.Triangulation M.plane Z)
  (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (SpatialEnvelope.clip M.plane Z)).Nonempty)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Truncation retains every original corner, so it still covers every actual curvature vertex. -/
theorem truncatedCutEmbedding_covers_positive_curvature (convex : Convex ℝ slopes)
    (v : T.pairedComplex.Vertex Set.univ)
    (curved : 0 < T.pairedComplex.interiorAngularDefect Set.univ v) :
    (T.roof conforming inside).projectedVertex v ∈
      (K.truncatedCutEmbedding compact nonempty R no_boundary level higher).carrier := by
  obtain ⟨⟨f, i⟩, equal, _height⟩ := K.clippedPhysical_positive_curvature_original_corner
    compact nonempty M T conforming inside convex v curved
  have corner := FiniteEmbeddedGraph.mem_carrier_vertex
    (K.truncatedCutEmbedding compact nonempty R no_boundary level higher)
    (Sum.inl (C.vertexOfCorner Set.univ (f, i)))
  change K.projectedVertex (C.vertexOfCorner Set.univ (f, i)) ∈ _ at corner
  rw [K.projectedVertex_ofCorner] at corner
  exact equal ▸ corner

end Unfoldings.ConvexRoof
