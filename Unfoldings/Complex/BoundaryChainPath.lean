module

public import Unfoldings.Complex.BoundaryChainTrace
public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Topology.FinitePathRange

/-! Continuous intrinsic boundary paths retain exactly their original bank traces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- Every original start copy and the final original endpoint in their actual chain order. -/
def boundaryChainPoint (j : Fin (n + 2)) : C.Realization retain :=
  Fin.lastCases
    (C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last)))
    (fun i => C.vertexPoint retain (C.boundaryEndVertex retain (chain.point i))) j

@[simp] theorem boundaryChainPoint_castSucc (i : Fin (n + 1)) :
    C.boundaryChainPoint chain i.castSucc =
      C.vertexPoint retain (C.boundaryEndVertex retain (chain.point i)) :=
  Fin.lastCases_castSucc i

@[simp] theorem boundaryChainPoint_last :
    C.boundaryChainPoint chain (Fin.last (n + 1)) =
      C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last)) :=
  Fin.lastCases_last

/-- Actual boundary successors meet at their same intrinsic cut-vertex copy. -/
theorem boundaryChainPoint_succ (i : Fin (n + 1)) :
    C.boundaryChainPoint chain i.succ =
      C.vertexPoint retain (C.boundaryEndVertex retain
        (C.boundaryTurn retain (chain.point i))) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.succ_last, C.boundaryChainPoint_last]
    rfl
  · change C.boundaryChainPoint chain k.succ.castSucc = _
    rw [C.boundaryChainPoint_castSucc, ← chain.next k]
    exact congrArg (C.vertexPoint retain) (C.boundaryMate_spec retain _).2

/-- The original directed bank, with its literal start and finish as path endpoints. -/
def boundaryChainLink (i : Fin (n + 1)) :
    Path (C.boundaryChainPoint chain i.castSucc) (C.boundaryChainPoint chain i.succ) where
  toFun := C.directedBoundaryPath (chain.point i)
  continuous_toFun := C.continuous_directedBoundaryPath _
  source' := (C.directedBoundaryPath_zero _).trans (C.boundaryChainPoint_castSucc chain i).symm
  target' := (C.directedBoundaryPath_one _).trans (C.boundaryChainPoint_succ chain i).symm

/-- Traverse every original bank continuously, keeping the actual intrinsic endpoint copies. -/
def boundaryChainPath : Path (C.boundaryChainPoint chain 0)
    (C.boundaryChainPoint chain (Fin.last (n + 1))) :=
  finitePathConcat (C.boundaryChainPoint chain) (C.boundaryChainLink chain)

/-- The continuous path traverses exactly the entire original intrinsic boundary chain. -/
theorem boundaryChainPath_range : Set.range (C.boundaryChainPath chain) =
    C.boundaryChainTrace chain := by
  rw [boundaryChainPath, path_concat_range, C.boundaryChainTrace_eq_union_paths]
  change {C.boundaryChainPoint chain 0} ∪
    (⋃ i, Set.range (C.directedBoundaryPath (chain.point i))) = _
  apply Set.union_eq_right.mpr
  intro p member
  rw [Set.mem_singleton_iff.mp member]
  exact Set.mem_iUnion.mpr ⟨0, 0, (C.boundaryChainLink chain 0).source⟩

/-- The same traversal with explicit original endpoint names. This form keeps physical
map composition independent of unfolding the whole finite chain in the elaborator. -/
def boundaryChainTraversal :
    Path (C.vertexPoint retain (C.boundaryEndVertex retain chain.first))
      (C.vertexPoint retain (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last))) :=
  (C.boundaryChainPath chain).cast
    (C.boundaryChainPoint_castSucc chain 0).symm (C.boundaryChainPoint_last chain).symm

theorem boundaryChainTraversal_range : Set.range (C.boundaryChainTraversal chain) =
    C.boundaryChainTrace chain := by
  change Set.range (C.boundaryChainPath chain) = _
  exact C.boundaryChainPath_range chain

/-- The same actual boundary traversal in any continuous target metric model. -/
def mappedBoundaryChainTraversal {X : Type*} [TopologicalSpace X]
    (map : C.Realization retain → X) (continuous : Continuous map) :
    Path (map (C.vertexPoint retain (C.boundaryEndVertex retain chain.first)))
      (map (C.vertexPoint retain
        (C.boundaryEndVertex retain (C.boundaryTurn retain chain.last)))) :=
  (C.boundaryChainTraversal chain).map continuous

theorem mappedBoundaryChainTraversal_range {X : Type*} [TopologicalSpace X]
    (map : C.Realization retain → X) (continuous : Continuous map) :
    Set.range (C.mappedBoundaryChainTraversal chain map continuous) =
      map '' C.boundaryChainTrace chain := by
  change Set.range (map ∘ C.boundaryChainTraversal chain) = _
  rw [Set.range_comp, C.boundaryChainTraversal_range]

end Unfoldings.TriangleComplex
