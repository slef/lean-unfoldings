module

public import Unfoldings.Complex.BoundaryGraph
public import Unfoldings.Topology.GraphFinitePath

/-! Actual closed bank orders yield multigraph cycles; no boundary bank is a bridge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

theorem boundaryCycle_isCycleThrough {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first) :
    (C.boundaryGraph retain).graph.IsCycleThrough (C.boundaryEndEquiv retain cycle.last).1
      (C.boundaryEndAsVertex retain cycle.first) (C.boundaryEndAsVertex retain cycle.last)
      (List.ofFn (fun i : Fin n => (C.boundaryEndEquiv retain (cycle.point i.castSucc)).1)) := by
  apply Graph.isCycleThrough_of_fin_sequence _
    (fun i => C.boundaryEndAsVertex retain (cycle.point i))
    (fun i => (C.boundaryEndEquiv retain (cycle.point i)).1)
  · intro i
    exact Set.mem_univ _
  · intro i
    have link := C.boundaryGraph_bank_link retain (cycle.point i.castSucc)
    have next := cycle.next i
    change C.boundaryMate retain (C.boundaryTurn retain (cycle.point i.castSucc)) =
      cycle.point i.succ at next
    have endpoints : C.boundaryEndAsVertex retain (C.boundaryTurn retain (cycle.point i.castSucc)) =
        C.boundaryEndAsVertex retain (cycle.point i.succ) := by
      rw [← next, C.boundaryEndAsVertex_mate]
    rwa [endpoints] at link
  · have link := C.boundaryGraph_bank_link retain cycle.last
    have endpoints : C.boundaryEndAsVertex retain (C.boundaryTurn retain cycle.last) =
        C.boundaryEndAsVertex retain cycle.first := by
      rw [← closes, C.boundaryEndAsVertex_mate]
    rwa [endpoints] at link
  · intro i j same
    exact C.boundaryCycle_vertices_injective retain cycle closes
      (congrArg (fun v : C.BoundaryVertex retain => v.val) same)
  · exact C.boundaryChain_banks_injective retain cycle

theorem boundaryGraph_bank_liesOnCycle (bank : C.BoundaryBank retain) :
    (C.boundaryGraph retain).graph.LiesOnCycle bank := by
  let p := (C.boundaryEndEquiv retain).symm (bank, false)
  obtain ⟨n, cycle, first, closes⟩ := C.exists_boundaryCycle retain (C.boundaryMate retain p)
  have last : cycle.last = C.boundaryTurn retain p := by
    apply (C.boundaryTurn_involutive retain).injective
    rw [C.boundaryTurn_involutive]
    exact (C.boundaryMate_involutive retain).injective (closes.trans first)
  have edge_equal : (C.boundaryEndEquiv retain cycle.last).1 = bank := by
    rw [last]
    simp only [boundaryTurn, Equiv.apply_symm_apply, p]
  have actual := C.boundaryCycle_isCycleThrough retain cycle closes
  rw [edge_equal] at actual
  exact actual.liesOnCycle

theorem boundaryGraph_bank_not_bridge (bank : C.BoundaryBank retain) :
    ¬ (C.boundaryGraph retain).graph.IsBridge bank := by
  intro bridge
  exact bridge.not_liesOnCycle (C.boundaryGraph_bank_liesOnCycle retain bank)

end Unfoldings.TriangleComplex
