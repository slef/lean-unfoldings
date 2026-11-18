module

public import Unfoldings.Roof.CompletionProjectedBankFans
public import Unfoldings.Roof.CompletionChainSpatialParameters

/-! The actual physical refinement inserts no projected bank turn. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionProjectedChainFansIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- The named original bank determines every fine piece's actual parent face. -/
theorem block_parent_face (i : Fin (n + 1)) (j : Fin ((R.block i).length + 1)) :
    E.originalParent ((R.block i).chain.point j).val.1.1 =
      (C.boundaryEndEquiv retain (coarse.point i)).1.val.face := by
  have parent := congrArg
    (fun bank : E.originalComplex.BoundaryBank (E.originalRetain retain) =>
      E.originalParent bank.val.face) ((R.block i).named j)
  have bank : (C.boundaryEndEquiv retain (coarse.point i)).1 = (R.label i).bank := by
    rw [← R.named i]
    exact congrArg Prod.fst ((C.boundaryEndEquiv retain).apply_symm_apply _)
  rw [bank]
  exact parent.trans (E.subdividedCutBank_parent retain (R.label i).seam
    (R.label i).side ((R.block i).index j))

open Classical in
/-- Each inserted bank vertex has exactly a straight projected cut-side fan. -/
theorem block_projected_totalAngle_eq_pi (i : Fin (n + 1)) (k : Fin (R.block i).length) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
        E.originalProjection_joined (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
          ((R.block i).chain.point k.succ))) = Real.pi := by
  let t := R.blockParameter i k.succ.castSucc
  have positive : 0 < t.val := by
    have before := R.blockParameter_strictMono i
      (show (0 : Fin ((R.block i).length + 2)) < k.succ.castSucc by
        change 0 < k.val + 1
        omega)
    rw [R.blockParameter_zero] at before
    exact before
  have small : t.val < 1 := by
    have before := R.blockParameter_strictMono i
      (show k.succ.castSucc < Fin.last ((R.block i).length + 1) by
        change k.val + 1 < (R.block i).length + 1
        omega)
    rw [R.blockParameter_last] at before
    exact before
  apply E.original_projected_fan_at_directed_bank_point
    ((R.block i).chain.point k.succ) (coarse.point i) t positive small (R.block_parent_face i _)
  let F := E.partition.pairedFolding.restrictFaces E.originalPieceSet
  have start := F.boundarySpatialChain_vertex_castSucc (R.block i).chain k.succ
  have physical := R.block_spatial_vertex_parameter i k.succ.castSucc
  have projection : E.originalBankEndProjection ((R.block i).chain.point k.succ) =
      Cap.horizontal (F.boundaryPosition ((R.block i).chain.point k.succ)) := by
    exact (((K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (E.partition.support ((R.block i).chain.point k.succ).val.1.1.val)).horizontal_place _).symm
      |>.trans (congrArg Cap.horizontal (F.boundaryPosition_raw _)).symm
  exact projection.trans ((congrArg Cap.horizontal start).symm.trans
    (congrArg Cap.horizontal physical))

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
