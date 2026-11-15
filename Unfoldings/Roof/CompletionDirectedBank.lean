module

public import Unfoldings.Roof.CompletionBankOrder
public import Unfoldings.Roof.CompletionInsertedAngles
public import Unfoldings.Complex.BoundaryContourPaths

/-! Ordered physical bank pieces follow the actual intrinsic boundary successor. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionDirectedBankIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The actual projected point of a directed original-piece bank end. -/
def originalBankEndProjection {retain : Set C.Seam}
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain)) : Plane :=
  E.pieceProjection p.val.1.1.val ((E.originalComplex.triangle p.val.1.1).vertex p.val.1.2)

open Classical in
theorem originalBankEndProjection_of_bank (retain : Set C.Seam)
    (bank : E.originalComplex.BoundaryBank (E.originalRetain retain)) (side : Bool) :
    E.originalBankEndProjection ((E.originalComplex.boundaryEndEquiv
      (E.originalRetain retain)).symm (bank, side)) =
        ((E.partition.projectedTriangle bank.val.face.val).endpoint bank.val.edge side).val := by
  cases side <;>
    exact ((K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (E.partition.support bank.val.face.val)).project.apply_symm_apply _

open Classical in
/-- Equal projected points in the same original parent are the very same fine cut vertex copy. -/
theorem original_boundaryEndVertex_eq_of_parent_projection (retain : Set C.Seam)
    (p q : E.originalComplex.BoundaryEnd (E.originalRetain retain))
    (parent : E.originalParent p.val.1.1 = E.originalParent q.val.1.1)
    (position : E.originalBankEndProjection p = E.originalBankEndProjection q) :
    E.originalComplex.boundaryEndVertex (E.originalRetain retain) p =
      E.originalComplex.boundaryEndVertex (E.originalRetain retain) q := by
  let S := E.originalSubdivision
  have coordinates : S.place p.val.1.1 ((E.originalComplex.triangle p.val.1.1).vertex p.val.1.2) =
      S.place q.val.1.1 ((E.originalComplex.triangle q.val.1.1).vertex q.val.1.2) := by
    change (K.projectFaceEquiv (E.originalParent p.val.1.1)).symm
      (E.originalBankEndProjection p) =
      (K.projectFaceEquiv (E.originalParent q.val.1.1)).symm (E.originalBankEndProjection q)
    rw [parent, position]
  have tagged := S.parentPoint_eq
    (y := (E.originalComplex.cornerPoint p.val.1).2)
    (x := (S.parentPoint (E.originalComplex.cornerPoint q.val.1)).2) parent coordinates
  apply E.originalComplex.vertexPoint_injective (E.originalRetain retain)
  apply (E.originalMetricEquiv retain).injective
  exact congrArg (MetricGluing.point C.Cell (C.glue retain)) tagged

open Classical in
/-- Turning one bank keeps its parent and exchanges its actual endpoint flag. -/
theorem originalBankEndProjection_turn (retain : Set C.Seam)
    (bank : E.originalComplex.BoundaryBank (E.originalRetain retain)) (side : Bool) :
    E.originalBankEndProjection (E.originalComplex.boundaryTurn (E.originalRetain retain)
      ((E.originalComplex.boundaryEndEquiv (E.originalRetain retain)).symm (bank, side))) =
        ((E.partition.projectedTriangle bank.val.face.val).endpoint bank.val.edge (!side)).val := by
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  exact E.originalBankEndProjection_of_bank retain bank (!side)

open Classical in
/-- The geometric order is the actual fine boundary chain, with every bank once. -/
theorem exists_original_cutBank_chain (retain : Set C.Seam) (s : C.CutSeam retain) (side : Bool)
    (G : OrderedSegmentPartition
      ((K.projectedTriangle (C.seamSide s.val side).face).vertex (C.seamSide s.val side).edge)
      ((K.projectedTriangle (C.seamSide s.val side).face).vertex
        (Triangle.next (C.seamSide s.val side).edge))
      (fun a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge =>
        (E.partition.projectedTriangle a.val.1.val).vertex a.val.2)
      (fun a : E.faceSidePieces (C.seamSide s.val side).face (C.seamSide s.val side).edge =>
        (E.partition.projectedTriangle a.val.1.val).vertex (Triangle.next a.val.2))) :
    ∃ c : (E.originalComplex.boundarySystem (E.originalRetain retain)).Chain G.length,
      ∀ i, (E.originalComplex.boundaryEndEquiv (E.originalRetain retain) (c.point i)).1 =
        E.subdividedCutBank retain s side (G.index i) ∧
        E.originalBankEndProjection (c.point i) = G.chain.vertex i.castSucc ∧
        E.originalBankEndProjection
          (E.originalComplex.boundaryTurn (E.originalRetain retain) (c.point i)) =
            G.chain.vertex i.succ := by
  classical
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let bank (i : Fin (G.length + 1)) := E.subdividedCutBank retain s side (G.index i)
  have flags (i : Fin (G.length + 1)) : ∃ b : Bool,
      ((E.partition.projectedTriangle (bank i).val.face.val).endpoint (bank i).val.edge b).val =
        G.chain.vertex i.castSucc ∧
      ((E.partition.projectedTriangle (bank i).val.face.val).endpoint (bank i).val.edge (!b)).val =
        G.chain.vertex i.succ := by
    rcases G.endpoints i with ⟨first, last⟩ | ⟨first, last⟩
    · exact ⟨false, first.symm, last.symm⟩
    · exact ⟨true, first.symm, last.symm⟩
  choose flag first last using flags
  let point (i : Fin (G.length + 1)) := (D.boundaryEndEquiv kept).symm (bank i, flag i)
  have named (i) : (D.boundaryEndEquiv kept (point i)).1 = bank i :=
    congrArg Prod.fst ((D.boundaryEndEquiv kept).apply_symm_apply (bank i, flag i))
  have starts (i) : E.originalBankEndProjection (point i) = G.chain.vertex i.castSucc :=
    (E.originalBankEndProjection_of_bank retain (bank i) (flag i)).trans (first i)
  have ends (i) : E.originalBankEndProjection (D.boundaryTurn kept (point i)) =
      G.chain.vertex i.succ :=
    (E.originalBankEndProjection_turn retain (bank i) (flag i)).trans (last i)
  have bank_injective : Function.Injective bank := by
    intro i j equal
    have same := congrArg (fun b : D.BoundaryBank kept => (b.val.face.val, b.val.edge)) equal
    have faces : (G.index i).val.1.val = (G.index j).val.1.val := by
      change (bank i).val.face.val = (bank j).val.face.val
      exact congrArg (fun b : E.partition.Index × Fin 3 => b.1) same
    have edges : (G.index i).val.2 = (G.index j).val.2 := by
      change (bank i).val.edge = (bank j).val.edge
      exact congrArg (fun b : E.partition.Index × Fin 3 => b.2) same
    apply G.index.injective
    exact Subtype.ext (Prod.ext (Subtype.ext faces) edges)
  have different (i j) : point i ≠ D.boundaryTurn kept (point j) := by
    intro equal
    have same := congrArg (fun p : D.BoundaryEnd kept => (D.boundaryEndEquiv kept p).1) equal
    simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply, named] at same
    have indices := bank_injective same
    subst j
    exact (D.boundaryTurn_ne kept (point i)) equal.symm
  have next (i : Fin G.length) : D.boundaryMate kept (D.boundaryTurn kept (point i.castSucc)) =
      point i.succ := by
    have parent : E.originalParent (D.boundaryTurn kept (point i.castSucc)).val.1.1 =
        E.originalParent (point i.succ).val.1.1 := by
      have first_parent := E.originalParent_eq (bank i.castSucc).val.face
        (G.index i.castSucc).val.1.property
      have last_parent := E.originalParent_eq (bank i.succ).val.face (G.index i.succ).val.1.property
      change E.originalParent (bank i.castSucc).val.face = E.originalParent (bank i.succ).val.face
      exact first_parent.trans last_parent.symm
    have equal := E.original_boundaryEndVertex_eq_of_parent_projection retain
      (D.boundaryTurn kept (point i.castSucc)) (point i.succ) parent (by
        rw [ends, starts, Fin.castSucc_succ])
    rcases (D.boundaryEnd_vertex_eq_iff kept (point i.succ)
      (D.boundaryTurn kept (point i.castSucc))).mp equal.symm with collision | adjacent
    · exact (different i.succ i.castSucc collision).elim
    · exact adjacent.symm
  refine ⟨⟨point, ?_, different, next⟩, fun i => ⟨named i, starts i, ends i⟩⟩
  intro i j equal
  have banks := congrArg (fun p : D.BoundaryEnd kept => (D.boundaryEndEquiv kept p).1) equal
  exact bank_injective ((named i).symm.trans (banks.trans (named j)))

end Unfoldings.ConvexRoof.CompletionMesh
