module

public import Unfoldings.FewestNets.ThreeExitEmbedding
public import Unfoldings.Geometry.StraightGraphPotential
public import Unfoldings.Roof.PrescribedSegmentMesh
public import Unfoldings.Roof.PotentialCutDisk
public import Unfoldings.Roof.PotentialContourHistory
public import Unfoldings.Complex.ContourSourceCoverage
public import Unfoldings.Roof.SeamSegments

/-! Mesh the actual component extension along its directed original stems and exit rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty}
  {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "U" => K.selectionComponent slopes seed
local notation "S" => K.restrictedCarrier U
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ S}
local notation "G" => K.componentClippedExtension
  (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))

variable (level : ℝ)
variable (M : SlopeEnvelope.FiniteSlopeModel
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty))
variable {a : ℝ} (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)

local instance threeExitMeshVertexFintype : Fintype V := Fintype.ofFinite V

local notation "idx" => Fintype.equivFin V
local notation "A" => R.truncatedParents
local notation "Forest[" higher "]" => R.truncatedEmbedding level higher
local notation "CutRank[" higher "]" => FiniteEmbeddedGraph.interpolatedRank (Forest[higher])
  (AscendingParents.height A)
local notation "Cuts[" higher "]" => FiniteEmbeddedGraph.carrier (Forest[higher])

/-- Every original triangle line is retained, including the boundary of the selected patch. -/
def originalEquations (K : ConvexRoof C) (i : Fin (Fintype.card Face) × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord i.2

theorem originalEquations_ne_zero (K : ConvexRoof C) (i : Fin (Fintype.card Face) × Fin 3) :
    originalEquations K i ≠ 0 :=
  (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord_ne_zero i.2

def meshInteriorVertex : V :=
  ⟨C.vertexOfCorner Set.univ (seed, 0), by
    rw [K.projectedVertex_ofCorner]
    exact Set.mem_iUnion.mpr ⟨⟨seed, K.seed_mem_selectionComponent slopes seed⟩,
      (K.projectedTriangle seed).vertex_mem 0⟩⟩

def fineMeshCutFirst (i : Fin (Fintype.card V)) : Plane := p ((idx).symm i)

def fineMeshCutLast (i : Fin (Fintype.card V)) : Plane := R.cutLast level ((idx).symm i)

theorem fineMeshCutEndpoints_ne (i : Fin (Fintype.card V))
    (higher : ∀ v : V, (G).height (p v) < level) :
    fineMeshCutFirst (K := K) (slopes := slopes) (seed := seed) i ≠ R.fineMeshCutLast level i :=
  R.cutLast_ne_cutFirst level higher ((idx).symm i)

local notation "initial" => fineMeshCutFirst (K := K) (slopes := slopes) (seed := seed)
local notation "terminal" => R.fineMeshCutLast level
local notation "Distinct[" higher "]" => (fun i => R.fineMeshCutEndpoints_ne level i higher)
local notation "sectionPoint" => p (meshInteriorVertex (K := K) (slopes := slopes) (seed := seed))

include M in
theorem meshSection_nonempty (higher : ∀ v : V, (G).height (p v) < level) :
    (interior (SpatialEnvelope.clip (SlopeEnvelope.FiniteSlopeModel.plane M) (-level))).Nonempty := by
  rw [M.clip_eq_sublevel, neg_neg]
  exact ⟨sectionPoint, (G).mem_interior_sublevel (higher _)⟩

theorem meshSection_point (higher : ∀ v : V, (G).height (p v) < level) :
    -level < -(G).height sectionPoint := by linarith only [higher meshInteriorVertex]

/-- The actual finite physical roof section includes the cut supporting lines and endpoints. -/
def fineMesh (higher : ∀ v : V, (G).height (p v) < level) : SpatialEnvelope.ConstrainedTriangulation (SlopeEnvelope.FiniteSlopeModel.plane M)
    (Sum.elim (originalEquations K) (segmentEquations initial terminal (Distinct[higher]))) (-level) :=
  M.prescribedSegmentMesh (originalEquations K) (originalEquations_ne_zero K) initial terminal (Distinct[higher])
    positive inner_disk (meshSection_point (K := K) (slopes := slopes) (seed := seed) level higher)

local notation "Mesh[" higher "]" => R.fineMesh level M positive inner_disk higher

theorem fineMesh_conforming (higher : ∀ v : V, (G).height (p v) < level) : TriangleFamily.Conforming (Mesh[higher]).projectedTriangle :=
  M.prescribedSegmentMesh_conforming (originalEquations K) (originalEquations_ne_zero K)
    initial terminal (Distinct[higher]) positive inner_disk (meshSection_point (K := K) (slopes := slopes) (seed := seed) level higher)

local notation "Roof[" higher "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation (Mesh[higher]))
  (R.fineMesh_conforming level M positive inner_disk higher)
  ((meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher))

local instance threeExitFineIndexFintype (higher : ∀ v : V, (G).height (p v) < level) : Fintype (Mesh[higher]).Index :=
  @Fintype.ofFinite _ (Mesh[higher]).finite

/-- The fine original seam advances along one prescribed parent edge.
The interpolated graph rank controls this ascent at every subdivision vertex. -/
theorem exists_fine_forward_seam (higher : ∀ v : V, (G).height (p v) < level) (v : (Mesh[higher]).pairedComplex.Vertex Set.univ)
    (internal : ¬ (Mesh[higher]).pairedComplex.IsBoundaryVertex Set.univ v)
    (on_cut : (Roof[higher]).projectedVertex v ∈ Cuts[higher]) :
    ∃ w s, (Mesh[higher]).pairedComplex.seamGraph.IsLink s v w ∧
      CutRank[higher] ((Roof[higher]).projectedVertex v) < CutRank[higher] ((Roof[higher]).projectedVertex w) ∧
      ((Roof[higher]).projectedTriangle ((Mesh[higher]).pairedComplex.left s).face).edge
        ((Mesh[higher]).pairedComplex.left s).edge ⊆ Cuts[higher] := by
  let roof := Roof[higher]
  let x := roof.projectedVertex v
  have x_in : x ∈ interior {z | (G).height z ≤ level} := by
    have member := (roof.projectedVertex_mem_interior_iff v).mpr internal
    rw [(Mesh[higher]).toTriangulation.roof_footprint, M.clip_eq_sublevel, neg_neg] at member
    exact member
  obtain ⟨u, along, before⟩ := R.exists_truncated_forward_piece level higher on_cut x_in
  let i := idx u
  have start_eq : initial i = p u := congrArg p ((idx).symm_apply_apply u)
  have last_eq : terminal i = R.cutLast level u :=
    congrArg (R.cutLast level) ((idx).symm_apply_apply u)
  obtain ⟨w, s, link, forward, different⟩ :=
    M.prescribedSegmentMesh_forward_seam (originalEquations K) (originalEquations_ne_zero K)
      initial terminal (Distinct[higher]) positive inner_disk (meshSection_point (K := K) (slopes := slopes) (seed := seed) level higher)
      ((meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)) i
      (by rw [start_eq, neg_neg]; exact (higher u).le)
      (by rw [last_eq, neg_neg]; exact R.cutLast_height_le level higher u)
      v internal (by rw [start_eq, last_eq]; exact along) (by rw [last_eq]; exact before)
  rw [last_eq] at forward
  let edge : {y // y ∉ (A).roots} := ⟨Sum.inl u,
    R.stems.choice.parents.withLeaves_inl_nonroot R.leafRank R.height_lt_leafRank u⟩
  have straight := R.truncatedEmbedding_straight level higher
  obtain ⟨history, which⟩ := straight.exists_orientedSubsegment_of_forward
    edge along before forward different
  have rises :
      (A).height ((Forest[higher]).left history.edge) < (A).height ((Forest[higher]).right history.edge) := by
    rw [which]
    exact (A).ascending edge.val edge.property
  refine ⟨w, s, link, straight.rank_lt_of_orientedSubsegment history rises, ?_⟩
  rw [← roof.projected_link_segment link, R.truncatedEmbedding_carrier_eq level higher]
  have included := (convex_segment (p u) (R.cutLast level u)).segment_subset along
    (right_mem_segment ℝ _ _)
  exact ((convex_segment (p u) (R.cutLast level u)).segment_subset along (included forward)).trans
    (Set.subset_iUnion (fun u : V => segment ℝ (p u) (R.cutLast level u)) u)

/-- Fine parents follow the already oriented geometric cut carrier. -/
def fineMeshForest (higher : ∀ v : V, (G).height (p v) < level) : (Roof[higher]).PotentialCutForest (CutRank[higher]) (Cuts[higher]) :=
  (Roof[higher]).potentialCutForest (CutRank[higher]) (Cuts[higher])
    (R.exists_fine_forward_seam level M positive inner_disk higher)

/-- All positive curvature of the finite extension lies on its prescribed mesh cuts. -/
theorem fineMesh_curvature_covered (higher : ∀ v : V, (G).height (p v) < level) (v : (Mesh[higher]).pairedComplex.Vertex Set.univ)
    (curved : 0 < (Mesh[higher]).pairedComplex.interiorAngularDefect Set.univ v) :
    (Roof[higher]).projectedVertex v ∈ Cuts[higher] := by
  obtain ⟨⟨f, j⟩, equal, _⟩ := K.componentClippedPhysical_positive_curvature_retained_corner
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty M
    (Mesh[higher]).toTriangulation (R.fineMesh_conforming level M positive inner_disk higher)
    ((meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)) B.convex v curved
  let w : V := ⟨C.vertexOfCorner Set.univ (f.val, j), by
    rw [K.projectedVertex_ofCorner]
    exact Set.mem_iUnion.mpr ⟨f, (K.projectedTriangle f.val).vertex_mem j⟩⟩
  exact equal ▸ (Forest[higher]).mem_carrier_vertex (.inl w)

theorem fineMesh_cuts_eq_segments (higher : ∀ v : V, (G).height (p v) < level) :
    Cuts[higher] = ⋃ i, segment ℝ (initial i) (terminal i) := by
  rw [R.truncatedEmbedding_carrier_eq level higher]
  ext x
  constructor
  · intro member
    obtain ⟨v, on_segment⟩ := Set.mem_iUnion.mp member
    refine Set.mem_iUnion.mpr ⟨idx v, ?_⟩
    change x ∈ segment ℝ (p ((idx).symm (idx v))) (R.cutLast level ((idx).symm (idx v)))
    simpa only [Equiv.symm_apply_apply] using on_segment
  · intro member
    obtain ⟨i, on_segment⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨(idx).symm i, on_segment⟩

/-- Every whole fine seam contained in the cut set lies in a single coarse edge. -/
theorem fineMesh_seam_subsegment (higher : ∀ v : V, (G).height (p v) < level)
    {s : (Mesh[higher]).pairedComplex.Seam}
    {x y : (Mesh[higher]).pairedComplex.Vertex Set.univ}
    (link : (Mesh[higher]).pairedComplex.seamGraph.IsLink s x y)
    (covered : ((Roof[higher]).projectedTriangle ((Mesh[higher]).pairedComplex.left s).face).edge
        ((Mesh[higher]).pairedComplex.left s).edge ⊆ Cuts[higher]) :
    ∃ i, (Roof[higher]).projectedVertex x ∈ segment ℝ (initial i) (terminal i) ∧
      (Roof[higher]).projectedVertex y ∈ segment ℝ (initial i) (terminal i) := by
  have same := (Roof[higher]).projected_link_segment link
  have projected := (Mesh[higher]).toTriangulation.roof_projectedTriangle
    (R.fineMesh_conforming level M positive inner_disk higher)
    (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher)
    ((Mesh[higher]).pairedComplex.left s).face
  rw [projected, R.fineMesh_cuts_eq_segments level higher] at covered
  rw [projected] at same
  obtain ⟨i, contained⟩ := M.prescribedSegmentMesh_subedge (originalEquations K)
    (originalEquations_ne_zero K) initial terminal (Distinct[higher]) positive inner_disk
    (meshSection_point (K := K) (slopes := slopes) (seed := seed) level higher)
    ((Mesh[higher]).pairedComplex.left s) covered
  exact ⟨i, contained (same ▸ left_mem_segment ℝ _ _),
    contained (same ▸ right_mem_segment ℝ _ _)⟩

/-- Fine seams oriented by increasing rank retain both parameters of the coarse edge. -/
theorem fineMesh_edge_orientation (higher : ∀ v : V, (G).height (p v) < level)
    {s : (Mesh[higher]).pairedComplex.Seam}
    {x y : (Mesh[higher]).pairedComplex.Vertex Set.univ}
    (link : (Mesh[higher]).pairedComplex.seamGraph.IsLink s x y)
    (covered : ((Roof[higher]).projectedTriangle ((Mesh[higher]).pairedComplex.left s).face).edge
        ((Mesh[higher]).pairedComplex.left s).edge ⊆ Cuts[higher])
    (increase : CutRank[higher] ((Roof[higher]).projectedVertex x) <
      CutRank[higher] ((Roof[higher]).projectedVertex y)) :
    Nonempty ((Forest[higher]).OrientedSubsegment
      ((Roof[higher]).projectedVertex x) ((Roof[higher]).projectedVertex y)) := by
  obtain ⟨i, first, last⟩ :=
    R.fineMesh_seam_subsegment level M positive inner_disk higher link covered
  obtain ⟨α, α_mem, at_first⟩ := (segment_eq_image_lineMap ℝ _ _).subset first
  obtain ⟨β, β_mem, at_last⟩ := (segment_eq_image_lineMap ℝ _ _).subset last
  let u := (idx).symm i
  let edge : {v // v ∉ (A).roots} := ⟨.inl u,
    R.stems.choice.parents.withLeaves_inl_nonroot R.leafRank R.height_lt_leafRank u⟩
  have grows := (R.truncatedEmbedding_straight level higher).interpolatedRank_strict edge
    ((A).ascending edge.val edge.property)
  have ordered : α < β := by
    by_contra reversed
    have later := grows.monotoneOn β_mem α_mem (not_lt.mp reversed)
    change CutRank[higher] (AffineMap.lineMap (initial i) (terminal i) β) ≤
      CutRank[higher] (AffineMap.lineMap (initial i) (terminal i) α) at later
    rw [at_first, at_last] at later
    exact increase.not_ge later
  exact ⟨⟨edge, α, β, α_mem, β_mem, ordered, at_first, at_last⟩⟩

local notation "FineForest[" higher "]" => R.fineMeshForest level M positive inner_disk higher
local notation "FineComplex[" higher "]" =>
  SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation (Mesh[higher]))


/-- The actual selected parent seam follows the orientation of its coarse cut. -/
theorem fineMesh_parent_alignment (higher : ∀ v : V, (G).height (p v) < level)
    (x : (FineComplex[higher]).Vertex Set.univ)
    (nonroot : x ∉ (FineForest[higher]).parents.roots) :
    Nonempty ((Forest[higher]).OrientedSubsegment ((Roof[higher]).projectedVertex x)
      ((Roof[higher]).projectedVertex ((FineForest[higher]).parents.parent x))) := by
  let F := FineForest[higher]
  let v : {v // v ∉ F.parents.roots} := ⟨x, nonroot⟩
  have strict := F.parents.ascending x nonroot
  rw [F.height_eq] at strict
  exact R.fineMesh_edge_orientation level M positive inner_disk higher
    (F.selection.link v) (F.selected_subset v) strict

/-- Distinct endpoints of a whole cut seam have distinct interpolated ranks. -/
theorem fineMesh_cut_rank_ne (higher : ∀ v : V, (G).height (p v) < level)
    {s : (FineComplex[higher]).Seam} {x y : (FineComplex[higher]).Vertex Set.univ}
    (link : (FineComplex[higher]).seamGraph.IsLink s x y)
    (covered : ((Roof[higher]).projectedTriangle ((FineComplex[higher]).left s).face).edge
        ((FineComplex[higher]).left s).edge ⊆ Cuts[higher]) :
    CutRank[higher] ((Roof[higher]).projectedVertex x) ≠
      CutRank[higher] ((Roof[higher]).projectedVertex y) := by
  obtain ⟨i, first, last⟩ := R.fineMesh_seam_subsegment level M positive inner_disk higher
    link covered
  obtain ⟨s₀, s₀_mem, at_first⟩ := (segment_eq_image_lineMap ℝ _ _).subset first
  obtain ⟨s₁, s₁_mem, at_last⟩ := (segment_eq_image_lineMap ℝ _ _).subset last
  let u := (idx).symm i
  let e : {v // v ∉ (A).roots} := ⟨.inl u,
    R.stems.choice.parents.withLeaves_inl_nonroot R.leafRank R.height_lt_leafRank u⟩
  have grows := (R.truncatedEmbedding_straight level higher).interpolatedRank_strict e
    ((A).ascending e.val e.property)
  intro equal
  have arg_eq := grows.injOn s₀_mem s₁_mem (at_first ▸ at_last ▸ equal)
  have points_eq := at_first.symm.trans (arg_eq ▸ at_last)
  have vertices_eq := (Roof[higher]).seamEmbedding.vertex_injective points_eq
  exact (Roof[higher]).seamEmbedding_straight.endpoints_ne s
    (by rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact vertices_eq
        · exact vertices_eq.symm)

/-- A forward fine seam in the prescribed cuts is the chosen parent at its start. -/
theorem fineMesh_selected_of_forward (higher : ∀ v : V, (G).height (p v) < level)
    {s : (FineComplex[higher]).Seam} {x y : (FineComplex[higher]).Vertex Set.univ}
    (link : (FineComplex[higher]).seamGraph.IsLink s x y)
    (covered : ((Roof[higher]).projectedTriangle ((FineComplex[higher]).left s).face).edge
        ((FineComplex[higher]).left s).edge ⊆ Cuts[higher])
    (increase : CutRank[higher] ((Roof[higher]).projectedVertex x) <
      CutRank[higher] ((Roof[higher]).projectedVertex y)) :
    s ∈ Set.range (FineForest[higher]).selection.edge := by
  let Q := Roof[higher]
  let F := FineForest[higher]
  obtain ⟨P⟩ := R.fineMesh_edge_orientation level M positive inner_disk higher link covered increase
  have on_cut : Q.projectedVertex x ∈ Cuts[higher] :=
    covered ((Q.projected_link_segment link) ▸ left_mem_segment ℝ _ _)
  have strict : (G).height (Q.projectedVertex x) < level := by
    obtain ⟨⟨v | r, member⟩, s₀, s₁, s₀_mem, s₁_mem, increasing, at_first, at_last⟩ := P
    · change AffineMap.lineMap (p v) (R.cutLast level v) s₀ = Q.projectedVertex x at at_first
      by_cases zero : s₀ = 0
      · rw [zero, AffineMap.lineMap_apply_zero] at at_first
        exact at_first ▸ higher v
      · apply R.truncatedSegment_height_lt level higher v
        rw [← at_first]
        exact lineMap_mem_openSegment ℝ _ _
          ⟨lt_of_le_of_ne s₀_mem.1 (Ne.symm zero), increasing.trans_le s₁_mem.2⟩
    · exact (member ⟨r, rfl⟩).elim
  have interior_point : Q.projectedVertex x ∈ interior Q.footprint := by
    rw [(Mesh[higher]).toTriangulation.roof_footprint, M.clip_eq_sublevel, neg_neg]
    exact (G).mem_interior_sublevel strict
  have nonroot : x ∉ F.parents.roots := by
    rw [F.roots_eq]
    rintro (boundary | outside)
    · exact (Q.projectedVertex_mem_interior_iff x).mp interior_point boundary
    · exact outside on_cut
  let e : {v // v ∉ F.parents.roots} := ⟨x, nonroot⟩
  obtain ⟨parent⟩ := R.fineMesh_parent_alignment level M positive inner_disk higher x nonroot
  have same := FiniteEmbeddedGraph.fine_forward_edge_unique (Forest[higher])
    (R.truncatedEmbedding_straight level higher) Subtype.val_injective
    Q.seamEmbedding_straight link (F.selection.link e) P parent
  exact ⟨e, same.symm⟩

/-- The retained fine seams are precisely those outside the prescribed cut carrier. -/
theorem fineMesh_retain_eq_prescribed (higher : ∀ v : V, (G).height (p v) < level) :
    (FineForest[higher]).retain = (Mesh[higher]).toTriangulation.retainOutside Cuts[higher] := by
  let T := (Mesh[higher]).toTriangulation
  let Q := Roof[higher]
  let F := FineForest[higher]
  have projection (f : T.Index) : Q.projectedTriangle f = T.projectedTriangle f :=
    T.roof_projectedTriangle (R.fineMesh_conforming level M positive inner_disk higher)
      (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M higher) f
  ext s
  constructor
  · intro kept
    by_contra outside
    have covered : (Q.projectedTriangle (T.pairedComplex.left s).face).edge
        (T.pairedComplex.left s).edge ⊆ Cuts[higher] := by
      rw [projection]
      exact not_not.mp outside
    have link : T.pairedComplex.seamGraph.IsLink s (T.pairedComplex.seamVertex s false)
        (T.pairedComplex.seamVertex s true) := Or.inl ⟨rfl, rfl⟩
    have distinct := R.fineMesh_cut_rank_ne level M positive inner_disk higher link covered
    rcases lt_or_gt_of_ne distinct with increasing | increasing
    · exact kept (R.fineMesh_selected_of_forward level M positive inner_disk higher
        link covered increasing)
    · exact kept (R.fineMesh_selected_of_forward level M positive inner_disk higher
        (Or.inr ⟨rfl, rfl⟩) covered increasing)
  · intro kept selected
    obtain ⟨e, rfl⟩ := selected
    apply kept
    have contained := F.selected_subset e
    rw [projection] at contained
    exact contained

/-- Follow an initial part of the fine vertex's actual parent path. -/
def fineMeshHistory (higher : ∀ v : V, (G).height (p v) < level)
    (x : (FineComplex[higher]).Vertex Set.univ) (n : ℕ) : PolygonalChain Plane n :=
  ⟨fun i => (Roof[higher]).projectedVertex ((FineForest[higher]).parents.parent^[i.val] x)⟩

theorem fineMeshHistory_aligned (higher : ∀ v : V, (G).height (p v) < level)
    (x : (FineComplex[higher]).Vertex Set.univ) (n : ℕ)
    (before : n ≤ (FineForest[higher]).parents.distanceToRoot x) (i : Fin n) :
    let H := R.fineMeshHistory level M positive inner_disk higher x n
    Nonempty ((Forest[higher]).OrientedSubsegment (H.vertex i.castSucc) (H.vertex i.succ)) := by
  let F := FineForest[higher]
  change Nonempty ((Forest[higher]).OrientedSubsegment
    ((Roof[higher]).projectedVertex (F.parents.parent^[i.val] x))
    ((Roof[higher]).projectedVertex (F.parents.parent^[i.val + 1] x)))
  rw [Function.iterate_succ_apply']
  exact R.fineMesh_parent_alignment level M positive inner_disk higher _
    (F.parents.iterate_lt_distanceToRoot_not_mem x (i.isLt.trans_le before))

/-- A contour based at a genuine rim root processes every positive curvature
vertex of the physical extension. -/
theorem exists_fineMesh_completeSourceContour (higher : ∀ v : V, (G).height (p v) < level) :
    ∃ contour : (FineComplex[higher]).BoundaryContour (FineForest[higher]).retain,
      (FineComplex[higher]).contourOriginalVertex (FineForest[higher]).selection contour 0 ∈
        (FineForest[higher]).parents.roots ∧
      (FineComplex[higher]).contourOriginalVertex (FineForest[higher]).selection contour
        (Fin.last contour.length) ∈ (FineForest[higher]).parents.roots ∧
      ∀ v : (FineComplex[higher]).Vertex Set.univ,
        0 < (FineComplex[higher]).interiorAngularDefect Set.univ v →
        ∃ e : (FineComplex[higher]).PositiveContourSource (FineForest[higher]).selection contour,
          (FineComplex[higher]).positiveContourVertex (FineForest[higher]).selection contour e = v := by
  let D := FineComplex[higher]
  let F := FineForest[higher]
  let saw := D.boundaryContourOfConnected F.retain
    ((Mesh[higher]).pairedFolding.boundaryGraph_connected_of_disk F.retain F.cutDisk)
  obtain ⟨contour, starts, ends⟩ := D.exists_contour_starts_ends_root_of_disk F.selection saw
    (Mesh[higher]).pairedFolding (Roof[higher]).diskHomeomorph F.boundary_roots
  refine ⟨contour, starts, ends, ?_⟩
  intro v curved
  have nonroot : v ∉ F.parents.roots := by
    intro root
    rw [F.roots_eq] at root
    rcases root with boundary | outside
    · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary] at curved
      exact (lt_irrefl _ curved)
    · exact outside (R.fineMesh_curvature_covered level M positive inner_disk higher v curved)
  exact D.exists_positiveContourSource_of_defect F.selection contour F.boundary_roots
    starts ends v nonroot curved

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
