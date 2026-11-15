module

public import Unfoldings.Roof.CompletionFacePatch
public import Unfoldings.Roof.CompletionOriginalConforming
public import Unfoldings.Complex.ClosedBanks
public import Unfoldings.Geometry.WholeEdgeSubdivision

/-! Whole original cut banks are covered by genuine physical fine bank edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBankSubdivisionIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Fine whole edges inside this original side, with their incident original face specified. -/
def faceSidePieces (f : Face) (e : Fin 3) : Set (E.facePieceSet f × Fin 3) :=
  {a | (E.partition.projectedTriangle a.1.val).edge a.2 ⊆ (K.projectedTriangle f).edge e}

open Classical in
/-- Every point of an old side, including old and fine endpoints, lies on such a whole fine edge. -/
theorem faceSidePieces_cover (f : Face) (e : Fin 3) :
    (K.projectedTriangle f).edge e =
      ⋃ a : E.faceSidePieces f e, (E.partition.projectedTriangle a.val.1.val).edge a.val.2 := by
  classical
  refine TriangleFamily.edge_eq_union_subedges
    (fun i : E.facePieceSet f => E.partition.projectedTriangle i.val) (K.projectedTriangle f) e
    ?_ (fun i k => E.mesh.signs i.val (f, k))
    (fun i k p member => E.mesh.constrained i.val p member (f, k))
  intro p member
  obtain ⟨i, contained, inside⟩ := E.original_face_covered_by_contained_pieces f p
    ((K.projectedTriangle f).edge_subset e member)
  exact Set.mem_iUnion.mpr ⟨⟨i, contained⟩, inside⟩

open Classical in
/-- Every original projected cut seam has both named side images in the actual geometric cut set. -/
theorem cut_seam_side_subset (retain : Set C.Seam) (s : C.CutSeam retain) (side : Bool) :
    (K.projectedTriangle (C.seamSide s.val side).face).edge (C.seamSide s.val side).edge ⊆
      K.projectedCutSet retain := by
  have first : (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge ⊆
      K.projectedCutSet retain := fun _ member =>
    Set.mem_iUnion.mpr ⟨s.val, Set.mem_iUnion.mpr ⟨s.property, member⟩⟩
  cases side
  · exact first
  · exact (K.projected_seam_edges_eq s.val).symm.subset.trans first

open Classical in
/-- A whole fine edge lying in an original cut is an actual unpaired bank of the cut complex. -/
theorem original_isBoundaryEdge_of_projected_subedge (retain : Set C.Seam)
    (a : EdgeRef E.originalPieceSet)
    (selected : (E.partition.projectedTriangle a.face.val).edge a.edge ⊆ K.projectedCutSet retain) :
    E.originalComplex.IsBoundaryEdge (E.originalRetain retain) a := by
  rintro ⟨s, kept, first | last⟩
  · apply kept
    have face := congrArg EdgeRef.face first
    have edge := congrArg EdgeRef.edge first
    change (E.partition.projectedTriangle (E.originalComplex.left s).face.val).edge
      (E.originalComplex.left s).edge ⊆ K.projectedCutSet retain
    simpa only [face, edge] using selected
  · apply kept
    change (E.partition.projectedTriangle (E.originalComplex.left s).face.val).edge
      (E.originalComplex.left s).edge ⊆ K.projectedCutSet retain
    change (E.partition.projectedTriangle (E.partition.pairedComplex.left s.val).face).edge
      (E.partition.pairedComplex.left s.val).edge ⊆ K.projectedCutSet retain
    rw [E.partition.paired_seam_projected_edge s.val]
    change (E.partition.projectedTriangle (E.originalComplex.right s).face.val).edge
      (E.originalComplex.right s).edge ⊆ K.projectedCutSet retain
    have face := congrArg EdgeRef.face last
    have edge := congrArg EdgeRef.edge last
    simpa only [face, edge] using selected

open Classical in
/-- A fine edge in a named old cut side is a genuine bank, even when other cuts meet at its ends. -/
def subdividedCutBank (retain : Set C.Seam) (s : C.CutSeam retain) (side : Bool)
    (a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge) :
    E.originalComplex.BoundaryBank (E.originalRetain retain) :=
  ⟨⟨⟨a.val.1.val, (C.seamSide s.val side).face, a.val.1.property⟩, a.val.2⟩,
    E.original_isBoundaryEdge_of_projected_subedge retain _
      (a.property.trans (cut_seam_side_subset (K := K) retain s side))⟩

open Classical in
/-- Matching projected coordinates identify actual points in the two cut metrics. -/
theorem originalMetricEquiv_bank_point (retain : Set C.Seam)
    (fine : E.originalComplex.BoundaryBank (E.originalRetain retain))
    (coarse : C.BoundaryBank retain)
    (parent : E.originalParent fine.val.face = coarse.val.face)
    (x : (E.originalComplex.triangle fine.val.face).Edge fine.val.edge)
    (y : (C.triangle coarse.val.face).Edge coarse.val.edge)
    (projected : E.pieceProjection fine.val.face.val x.val = K.projectFace coarse.val.face y.val) :
    E.originalMetricEquiv retain
      (E.originalComplex.bankMap (E.originalRetain retain) fine x) = C.bankMap retain coarse y := by
  have coordinates : E.originalSubdivision.place fine.val.face x.val = y.val := by
    change E.originalCoordinates fine.val.face.val (E.originalParent fine.val.face) x.val = _
    rw [parent]
    change (K.projectFaceEquiv coarse.val.face).symm
      (E.pieceProjection fine.val.face.val x.val) = _
    rw [projected]
    exact (K.projectFaceEquiv coarse.val.face).symm_apply_apply y.val
  have tagged := E.originalSubdivision.parentPoint_eq
    (y := (E.originalComplex.triangle fine.val.face).edgeMap fine.val.edge x)
    (x := (C.triangle coarse.val.face).edgeMap coarse.val.edge y) parent coordinates
  exact congrArg (MetricGluing.point C.Cell (C.glue retain)) tagged

open Classical in
/-- Whole fine bank images cover exactly the entire old cut bank in its actual cut metric. -/
theorem original_cutBank_eq_union_subdivided (retain : Set C.Seam)
    (s : C.CutSeam retain) (side : Bool) :
    Set.range (C.bankMap retain (C.cutBank retain s side)) =
      ⋃ a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge,
        Set.range (fun x => E.originalMetricEquiv retain
          (E.originalComplex.bankMap (E.originalRetain retain)
            (E.subdividedCutBank retain s side a) x)) := by
  classical
  let edge := C.seamSide s.val side
  let bank := C.cutBank retain s side
  have parent (a : E.faceSidePieces edge.face edge.edge) :
      E.originalParent (E.subdividedCutBank retain s side a).val.face = edge.face :=
    E.originalParent_eq _ a.val.1.property
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have projected : K.projectFace edge.face x.val ∈ (K.projectedTriangle edge.face).edge
        edge.edge := by
      rw [ConvexRoof.projectedTriangle, Triangle.affineImage_edge]
      exact ⟨x.val, x.property, rfl⟩
    rw [E.faceSidePieces_cover edge.face edge.edge] at projected
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp projected
    let y := (E.partition.edgeProjection a.val.1.val a.val.2).symm
      ⟨K.projectFace edge.face x.val, member⟩
    have coordinates : E.pieceProjection a.val.1.val y.val = K.projectFace edge.face x.val :=
      congrArg Subtype.val ((E.partition.edgeProjection a.val.1.val a.val.2).apply_symm_apply
        ⟨K.projectFace edge.face x.val, member⟩)
    exact Set.mem_iUnion.mpr ⟨a, y,
      E.originalMetricEquiv_bank_point retain (E.subdividedCutBank retain s side a) bank
        (parent a) y x coordinates⟩
  · intro member
    obtain ⟨a, x, rfl⟩ := Set.mem_iUnion.mp member
    let p := E.partition.edgeProjection a.val.1.val a.val.2 x
    have projected := a.property p.property
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_edge] at projected
    obtain ⟨y, inside, coordinates⟩ := projected
    exact ⟨⟨y, inside⟩,
      (E.originalMetricEquiv_bank_point retain (E.subdividedCutBank retain s side a) bank
        (parent a) x ⟨y, inside⟩ coordinates.symm).symm⟩

end Unfoldings.ConvexRoof.CompletionMesh
