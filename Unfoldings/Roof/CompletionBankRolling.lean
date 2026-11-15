module

public import Unfoldings.Roof.CompletionDirectedBank
public import Unfoldings.Complex.BoundaryChainRolling

/-! The actual fine boundary chain along an original bank has zero extra unreduced rolling turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionBankRollingIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- An actual bank end strictly between old bank endpoints has a straight intrinsic fan. -/
theorem original_bankEnd_totalAngle_at_open_bank (retain : Set C.Seam)
    (coarse : C.BoundaryBank retain)
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain))
    (parent : E.originalParent p.val.1.1 = coarse.val.face)
    {t : ℝ} (positive : 0 < t) (small : t < 1)
    (position : E.originalBankEndProjection p =
      AffineMap.lineMap ((K.projectedTriangle coarse.val.face).vertex coarse.val.edge)
        ((K.projectedTriangle coarse.val.face).vertex (Triangle.next coarse.val.edge)) t) :
    E.originalComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p) = Real.pi := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let fine := (D.boundaryEndEquiv kept p).1
  let flag := (D.boundaryEndEquiv kept p).2
  let x := (D.triangle fine.val.face).endpoint fine.val.edge flag
  let y : (C.triangle coarse.val.face).Edge coarse.val.edge :=
    ⟨_, lineMap_mem_segment ℝ _ _ ⟨positive.le, small.le⟩⟩
  have y_regular : ¬ C.IsVertex (C.edgePoint coarse.val y) :=
    (C.triangle coarse.val.face).lineMap_edge_not_vertex coarse.val.edge ⟨positive, small⟩
  have projected : E.pieceProjection fine.val.face.val x.val =
      K.projectFace coarse.val.face y.val := by
    have equal : E.pieceProjection fine.val.face.val x.val = E.originalBankEndProjection p := by
      change E.pieceProjection fine.val.face.val
        ((D.triangle fine.val.face).endpoint fine.val.edge flag).val = _
      obtain ⟨⟨bank, side⟩, rfl⟩ := (D.boundaryEndEquiv kept).symm.surjective p
      rcases bank with ⟨⟨face, edge⟩, boundary⟩
      cases side <;> fin_cases edge <;> rfl
    rw [equal, position]
    exact ((K.projectFace coarse.val.face).apply_lineMap _ _ t).symm
  have at_point := E.originalMetricEquiv_bank_point retain fine coarse parent x y projected
  rw [← D.boundaryEnd_vertexPoint_eq_endpoint p] at at_point
  exact E.original_totalAngle_at_bank_interior retain coarse y y_regular
    (D.boundaryEndVertex kept p) at_point

open Classical in
/-- Endpoint coordinates identify the exact original cut vertex copy in the metric equivalence. -/
theorem originalMetricEquiv_boundaryEnd_at_corner (retain : Set C.Seam)
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) (f : Face) (k : Fin 3)
    (parent : E.originalParent p.val.1.1 = f)
    (position : E.originalBankEndProjection p = (K.projectedTriangle f).vertex k) :
    E.originalMetricEquiv retain (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p)) =
        C.vertexPoint retain (C.vertexOfCorner retain (f, k)) := by
  let S := E.originalSubdivision
  have coordinates : S.place p.val.1.1 ((E.originalComplex.triangle p.val.1.1).vertex p.val.1.2) =
      (C.triangle f).vertex k := by
    change (K.projectFaceEquiv (E.originalParent p.val.1.1)).symm
      (E.originalBankEndProjection p) = _
    rw [parent, position]
    exact (K.projectFaceEquiv f).symm_apply_apply ((C.triangle f).vertex k)
  have tagged := S.parentPoint_eq (y := (E.originalComplex.cornerPoint p.val.1).2)
    (x := (C.cornerPoint (f, k)).2) parent coordinates
  exact congrArg (MetricGluing.point C.Cell (C.glue retain)) tagged

open Classical in
/-- Original bank endpoints retain their exact one-sided fan angle, including branching cuts. -/
theorem original_bankEnd_totalAngle_at_old_corner (retain : Set C.Seam)
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) (f : Face) (k : Fin 3)
    (parent : E.originalParent p.val.1.1 = f)
    (position : E.originalBankEndProjection p = (K.projectedTriangle f).vertex k) :
    E.originalComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p) =
        C.totalAngle retain (C.vertexOfCorner retain (f, k)) :=
  E.original_totalAngle_eq retain _ _
    (E.originalMetricEquiv_boundaryEnd_at_corner retain p f k parent position)

open Classical in
/-- The constructed ordered fine bank chain has exactly zero real heading on every prefix. -/
theorem exists_original_cutBank_chain_zero_heading (retain : Set C.Seam)
    (s : C.CutSeam retain) (side : Bool)
    (G : OrderedSegmentPartition
      ((K.projectedTriangle (C.seamSide s.val side).face).vertex (C.seamSide s.val side).edge)
      ((K.projectedTriangle (C.seamSide s.val side).face).vertex
        (Triangle.next (C.seamSide s.val side).edge))
      (fun a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge =>
        (E.partition.projectedTriangle a.val.1.val).vertex a.val.2)
      (fun a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge =>
        (E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2))) :
    ∃ c : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain G.length,
      (∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (c.point i)).1 =
        E.subdividedCutBank retain s side (G.index i)) ∧
      (∀ i, E.originalBankEndProjection (c.point i) = G.chain.vertex i.castSucc) ∧
      (∀ i, E.originalBankEndProjection
        (E.originalComplex.boundaryTurn (E.originalRetain retain) (c.point i)) =
          G.chain.vertex i.succ) ∧
      ∀ i, E.originalComplex.boundaryChainRollHeading c i = 0 := by
  classical
  let edge := C.seamSide s.val side
  let T := K.projectedTriangle edge.face
  let D := E.originalComplex
  let kept := E.originalRetain retain
  obtain ⟨c, agreement⟩ := E.exists_original_cutBank_chain retain s side G
  have first_coordinate : lineCoordinate (T.vertex edge.edge) (T.vertex (Triangle.next edge.edge))
      (G.chain.vertex 0) = 0 := by
    rw [G.start]
    simpa only [AffineMap.lineMap_apply_zero] using
      lineCoordinate_lineMap (T.edge_endpoints_ne edge.edge) 0
  have last_coordinate : lineCoordinate (T.vertex edge.edge) (T.vertex (Triangle.next edge.edge))
      (G.chain.vertex (Fin.last (G.length + 1))) = 1 := by
    rw [G.finish]
    simpa only [AffineMap.lineMap_apply_one] using
      lineCoordinate_lineMap (T.edge_endpoints_ne edge.edge) 1
  have straight (i : Fin G.length) :
      D.totalAngle kept (D.boundaryEndVertex kept (c.point i.succ)) = Real.pi := by
    let j := i.succ
    let p := c.point j
    let z := G.chain.vertex j.castSucc
    let t := lineCoordinate (T.vertex edge.edge) (T.vertex (Triangle.next edge.edge)) z
    have positive : 0 < t := by
      have bound := G.ordered (show (0 : Fin (G.length + 2)) < j.castSucc by
        change 0 < i.val + 1
        omega)
      change lineCoordinate (T.vertex edge.edge) (T.vertex (Triangle.next edge.edge))
        (G.chain.vertex 0) < t at bound
      rw [first_coordinate] at bound
      exact bound
    have small : t < 1 := by
      have bound := G.ordered (show j.castSucc < Fin.last (G.length + 1) by
        change i.val + 1 < G.length + 1
        omega)
      change t < lineCoordinate (T.vertex edge.edge) (T.vertex (Triangle.next edge.edge))
        (G.chain.vertex (Fin.last (G.length + 1))) at bound
      rw [last_coordinate] at bound
      exact bound
    have member : z ∈ T.edge edge.edge := by
      rcases G.endpoints j with first | last
      · rw [show z = _ from first.1]
        exact (G.index j).property (left_mem_segment ℝ _ _)
      · rw [show z = _ from last.1]
        exact (G.index j).property (right_mem_segment ℝ _ _)
    have parent : E.originalParent p.val.1.1 = edge.face := by
      change E.originalParent ((D.boundaryEndEquiv kept p).1).val.face = edge.face
      rw [(agreement j).1]
      exact E.originalParent_eq _ (G.index j).val.1.property
    apply E.original_bankEnd_totalAngle_at_open_bank retain (C.cutBank retain s side) p parent
      positive small
    exact (agreement j).2.1.trans
      (lineCoordinate_recover (T.edge_endpoints_ne edge.edge)
        (segment_subset_line _ _ member)).symm
  exact ⟨c, fun i => (agreement i).1, fun i => (agreement i).2.1,
    fun i => (agreement i).2.2, D.boundaryChainRollHeading_eq_zero c straight⟩

open Classical in
/-- Construct the full directed fine refinement of an old cut side, with exact real rolling. -/
theorem exists_original_cutBank_straight_roll (retain : Set C.Seam)
    (s : C.CutSeam retain) (side : Bool) :
    ∃ n : ℕ, ∃ c : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain n,
      (∀ i, E.originalComplex.boundaryChainRollHeading c i = 0) ∧
      E.originalBankEndProjection c.first =
        (K.projectedTriangle (C.seamSide s.val side).face).vertex (C.seamSide s.val side).edge ∧
      E.originalBankEndProjection
        (E.originalComplex.boundaryTurn (E.originalRetain retain) c.last) =
          (K.projectedTriangle (C.seamSide s.val side).face).vertex
            (Triangle.next (C.seamSide s.val side).edge) ∧
      ∃ index : Fin (n + 1) ≃
          E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge,
        ∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (c.point i)).1 =
          E.subdividedCutBank retain s side (index i) := by
  obtain ⟨G⟩ := E.exists_ordered_faceSidePieces (C.seamSide s.val side).face
    (C.seamSide s.val side).edge
  obtain ⟨c, named, first, last, heading⟩ :=
    E.exists_original_cutBank_chain_zero_heading retain s side G
  refine ⟨G.length, c, heading, ?_, ?_, G.index, named⟩
  · exact (first 0).trans G.start
  · change E.originalBankEndProjection
      (E.originalComplex.boundaryTurn (E.originalRetain retain) (c.point (Fin.last G.length))) = _
    have endpoint := last (Fin.last G.length)
    rw [Fin.succ_last] at endpoint
    exact endpoint.trans G.finish

end Unfoldings.ConvexRoof.CompletionMesh
