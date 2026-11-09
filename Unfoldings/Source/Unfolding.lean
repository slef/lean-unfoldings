module

public import Unfoldings.Source.Net
public import Unfoldings.Source.CompletedRadials
public import Unfoldings.Source.CutIntrinsic

/-!
# Constructed finite polygonal source unfoldings at every regular source

`SourceUnfolding` records the output of the construction: the actual source
frame, shortest-path coordinates, completed intrinsic disk, exact cut boundary,
and a finite nonoverlapping polygonal layout with compatible rigid face maps.
`ConvexBoundary.sourceUnfolding` constructs all these data from the geometric
convex-boundary hypotheses and a regular source; its input contains no cut-locus,
completion, polygonality, development, or nonoverlap conclusions.

The finite graph/tree characterization of the cut locus is a separate theorem.
Sources at genuine cone vertices require a sector-valued source frame and are
outside the regular-source theorem here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  [metric : MetricSpace (C.Realization Set.univ)]
  [@CompactSpace (C.Realization Set.univ)
    metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace]

structure SourceUnfolding (source : C.Realization Set.univ) where
  frame : SourceFrame source
  coordinate_injective : Function.Injective
    (fun p : SourcePath source => frame.coordinate p.path p.geodesic)
  compact : CompactSpace frame.cutCompletion
  complete : CompleteSpace frame.cutCompletion
  disk : frame.cutCompletion ≃ₜ Metric.closedBall (0 : Plane) 1
  cutComplement : ↥((sourceCutLocus source)ᶜ) ≃ₜ frame.cutInterior
  intrinsic_distance : ∀ a b : ↥((sourceCutLocus source)ᶜ),
    edist (cutComplement a) (cutComplement b) = Path.eDistance a b
  interior_projection : ∀ z : frame.cutInterior,
    frame.cutCompletionProjection coordinate_injective (frame.cutInteriorInclusion z) =
      (cutComplement.symm z).val
  inclusion_isometry : Isometry frame.cutInteriorInclusion
  inclusion_dense : DenseRange frame.cutInteriorInclusion
  projection_lipschitz : LipschitzWith 1 (frame.cutCompletionProjection coordinate_injective)
  projection_surjective : Function.Surjective (frame.cutCompletionProjection coordinate_injective)
  boundary_projection : frame.cutCompletionProjection coordinate_injective ''
    {z : frame.cutCompletion | z.val ∈ frontier frame.domain} = sourceCutLocus source
  Piece : Type
  finite_pieces : Fintype Piece
  layout : FacePolygonalLayout C Piece
  nonoverlapping : layout.Nonoverlapping
  fold_isometry : ∀ i, Isometry (layout.fold Set.univ i)
  footprint : layout.footprint = frame.domain
  folding : ∀ i (x : layout.region i), ∃ z : frame.domain, z.val = x.val ∧
    frame.projection coordinate_injective z = layout.fold Set.univ i x
  boundary_edges : Set (Plane × Plane)
  finite_boundary_edges : boundary_edges.Finite
  boundary_segments : frontier frame.domain = ⋃ e ∈ boundary_edges, segment ℝ e.1 e.2

namespace SourceUnfolding

variable {source : C.Realization Set.univ} (U : SourceUnfolding (C := C) source)

def piecePoint (i : U.Piece) (x : U.layout.region i) : U.frame.cutCompletion :=
  ⟨x.val, U.footprint ▸ U.layout.mem_footprint i x⟩

theorem piecePoint_isometry (i : U.Piece) : Isometry (U.piecePoint i) := by
  intro x y
  apply PolygonalPoint.edist_eq_of_segment
  intro z hz
  have member := (U.layout.convex_region i).segment_subset x.property y.property hz
  rw [← U.footprint]
  exact Set.mem_iUnion.mpr ⟨i, member⟩

theorem piecePoint_projection (i : U.Piece) (x : U.layout.region i) :
    U.frame.cutCompletionProjection U.coordinate_injective (U.piecePoint i x) =
      U.layout.fold Set.univ i x := by
  obtain ⟨z, equal, image⟩ := U.folding i x
  have same : PolygonalPoint.toSubtype (U.piecePoint i x) = z := Subtype.ext equal.symm
  change U.frame.projection U.coordinate_injective
    (PolygonalPoint.toSubtype (U.piecePoint i x)) = _
  rw [same]
  exact image

theorem piece_projection_isometry (i : U.Piece) : Isometry
    (fun x : U.layout.region i =>
      U.frame.cutCompletionProjection U.coordinate_injective (U.piecePoint i x)) := by
  have equal : (fun x : U.layout.region i =>
      U.frame.cutCompletionProjection U.coordinate_injective (U.piecePoint i x)) =
      U.layout.fold Set.univ i := funext (U.piecePoint_projection i)
  rw [equal]
  exact U.fold_isometry i

theorem development_injective :
    Function.Injective (PolygonalPoint.val (s := U.frame.domain)) :=
  U.frame.cutCompletion_development_injective

theorem radial_shortest_path (p : SourcePath source) :
    (U.frame.cutRadial p).IsGeodesic ∧
      ∀ t, U.frame.cutCompletionProjection U.coordinate_injective
        (U.frame.cutRadial p t) = p.path t :=
  ⟨U.frame.cutRadial_isGeodesic p, U.frame.cutRadial_projection U.coordinate_injective p⟩

theorem source_distance_preserved (z : U.frame.cutCompletion) :
    edist U.frame.cutOrigin z = ENNReal.ofReal (dist source
      (U.frame.cutCompletionProjection U.coordinate_injective z)) :=
  (U.frame.cutOrigin_distance_preserved U.coordinate_injective z).trans (edist_dist _ _)

end SourceUnfolding

end Unfoldings

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceCutComplement_intrinsic_distance :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (a b : ↥((sourceCutLocus source)ᶜ)),
      edist (P.sourceCutComplementHomeomorph R a) (P.sourceCutComplementHomeomorph R b) =
        Path.eDistance a b := by
  let := P.metricSpace
  intro source R a b
  let H := Homeomorph.setCongr (P.sourceRegularRegion_eq_cutComplement R).symm
  have equal := Path.eDistance_eq_of_homeomorph_local_center_bounds H
    (fun _ => Filter.Eventually.of_forall (fun _ => le_rfl))
    (fun _ => Filter.Eventually.of_forall (fun _ => le_rfl)) a b
  exact (P.sourceCutSurface_intrinsic_distance R (H a) (H b)).trans equal

theorem sourceCutComplement_projection :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.cutInterior),
      R.cutCompletionProjection (P.sourcePathCoordinate_injective R) (R.cutInteriorInclusion z) =
        ((P.sourceCutComplementHomeomorph R).symm z).val := by
  let := P.metricSpace
  intro source R z
  rfl

def sourceUnfolding :
    letI := P.metricSpace
    (source : C.Realization Set.univ) → C.IsRegularPoint Set.univ source →
      SourceUnfolding (C := C) source := by
  let := P.metricSpace
  intro source regular
  apply Classical.choice
  let R := sourceFrame regular
  obtain ⟨Piece, finite_Piece, layout, nonoverlap, footprint, folding⟩ :=
    P.exists_source_polygonal_net R
  obtain ⟨edges, finite_edges, boundary, _⟩ := P.exists_finite_source_boundary_segments R
  exact ⟨
    { frame := R
      coordinate_injective := P.sourcePathCoordinate_injective R
      compact := P.sourceCutCompletion_compact R
      complete := P.sourceCutCompletion_complete R
      disk := P.sourceCutDiskHomeomorph R
      cutComplement := P.sourceCutComplementHomeomorph R
      intrinsic_distance := P.sourceCutComplement_intrinsic_distance R
      interior_projection := P.sourceCutComplement_projection R
      inclusion_isometry := P.sourceCutInteriorInclusion_isometry R
      inclusion_dense := P.sourceCutInteriorInclusion_dense R
      projection_lipschitz := P.sourceCutCompletion_projection_lipschitz R
      projection_surjective :=
        R.cutCompletionProjection_surjective _ (P.sourcePath_target_surjective source)
      boundary_projection := P.sourceCutCompletion_boundary_projection_cutLocus R
      Piece := Piece
      finite_pieces := finite_Piece
      layout := layout
      nonoverlapping := nonoverlap
      fold_isometry := layout.fold_isometry F Set.univ
      footprint := footprint
      folding := folding
      boundary_edges := edges
      finite_boundary_edges := finite_edges
      boundary_segments := boundary }⟩

theorem source_unfolding_exists :
    letI := P.metricSpace
    ∀ (source : C.Realization Set.univ), C.IsRegularPoint Set.univ source →
      Nonempty (SourceUnfolding (C := C) source) := by
  let := P.metricSpace
  intro source regular
  exact ⟨P.sourceUnfolding source regular⟩

def sourceUnfoldingOfNonextreme :
    letI := P.metricSpace
    (source : C.Realization Set.univ) →
      F.toSpace Set.univ source ∉ F.vertexHull.extremePoints ℝ →
        SourceUnfolding (C := C) source := by
  let := P.metricSpace
  intro source outside
  apply P.sourceUnfolding source
  apply (P.isRegularPoint_iff_ne_extreme_vertices source).mpr
  intro v extreme equal
  apply outside
  rw [equal]
  exact extreme

end Unfoldings.SpatialFolding.ConvexBoundary
