module

public import Unfoldings.Complex.BoundarySingleCycle
public import Unfoldings.Complex.BoundaryJordan

/-! A bank cycle visiting every end has exactly the actual boundary as its carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

theorem boundaryCycle_banks_cover {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (covers : ∀ p, cycle.Visited p) (bank : C.BoundaryBank retain) :
    bank = (C.boundaryEndEquiv retain cycle.last).1 ∨
      bank ∈ List.ofFn
        (fun i : Fin n => (C.boundaryEndEquiv retain (cycle.point i.castSucc)).1) := by
  let p := (C.boundaryEndEquiv retain).symm (bank, false)
  obtain ⟨i, same | opposite⟩ := covers p
  all_goals
    have same_bank : bank = (C.boundaryEndEquiv retain (cycle.point i)).1 := by
      first
      | simpa only [p, Equiv.apply_symm_apply] using
          congrArg (fun q => (C.boundaryEndEquiv retain q).1) same
      | simpa only [p, boundarySystem, boundaryTurn, Equiv.apply_symm_apply] using
          congrArg (fun q => (C.boundaryEndEquiv retain q).1) opposite
    revert same_bank
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro same_bank
      exact Or.inl same_bank
    · intro same_bank
      exact Or.inr (List.mem_ofFn.mpr ⟨j, same_bank.symm⟩)

theorem boundaryCycle_edgesCover_eq {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (covers : ∀ p, cycle.Visited p) (f : C(C.Realization retain, Plane))
    (injective : Function.Injective f) :
    Graph.edgesCover ((C.boundaryGraph retain).mapEmbedding f injective).drawing
        ((C.boundaryEndEquiv retain cycle.last).1 ::
          List.ofFn (fun i : Fin n => (C.boundaryEndEquiv retain (cycle.point i.castSucc)).1)) =
      f '' C.bankBoundary retain := by
  let G := (C.boundaryGraph retain).mapEmbedding f injective
  ext p
  constructor
  · intro inside
    obtain ⟨bank, _member, arc⟩ := Graph.mem_edgesCover_iff.mp inside
    rw [G.drawing_edgeArc] at arc
    obtain ⟨t, equal⟩ := arc
    exact ⟨C.bankMap retain bank (C.bankParameter retain bank t),
      C.bankMap_mem_bankBoundary retain bank _, equal⟩
  · rintro ⟨x, boundary, rfl⟩
    obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp boundary
    obtain ⟨t, rfl⟩ := C.bankParameter_surjective retain bank y
    apply Graph.mem_edgesCover
    · rcases C.boundaryCycle_banks_cover retain cycle covers bank with same | member
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons.mpr (Or.inr member)
    · rw [G.drawing_edgeArc]
      exact ⟨t, rfl⟩

end Unfoldings.TriangleComplex
