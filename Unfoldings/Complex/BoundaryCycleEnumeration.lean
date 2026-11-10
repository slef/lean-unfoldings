module

public import Unfoldings.Complex.BoundarySingleCycle
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Enumerating the vertices and banks of one actual boundary cycle

A covering bank cycle visits each actual boundary vertex copy and each bank
exactly once. These equivalences permit sums over the geometric boundary to be
computed in cyclic order, independently of a planar development or its overlap.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
  (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first)

include closes in
/-- The far end of a bank is the next vertex of the closed cycle. -/
theorem boundaryCycle_next_vertex (i : Fin (n + 1)) :
    C.boundaryEndAsVertex retain (C.boundaryTurn retain (cycle.point i)) =
      C.boundaryEndAsVertex retain (cycle.point (finRotate (n + 1) i)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last]
    change C.boundaryEndAsVertex retain (C.boundaryTurn retain cycle.last) =
      C.boundaryEndAsVertex retain cycle.first
    rw [← closes, C.boundaryEndAsVertex_mate]
  · rw [show finRotate (n + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt]
    have joined := cycle.next j
    change C.boundaryMate retain (C.boundaryTurn retain (cycle.point j.castSucc)) =
      cycle.point j.succ at joined
    rw [← joined, C.boundaryEndAsVertex_mate]

variable (covers : ∀ p, cycle.Visited p)

/-- A covering cycle enumerates the actual banks, retaining their original names. -/
def boundaryCycleBankEquiv : Fin (n + 1) ≃ C.BoundaryBank retain :=
  Equiv.ofBijective (fun i => (C.boundaryEndEquiv retain (cycle.point i)).1) ⟨
    C.boundaryChain_banks_injective retain cycle, by
      intro bank
      let p := (C.boundaryEndEquiv retain).symm (bank, false)
      obtain ⟨i, same | same⟩ := covers p
      · refine ⟨i, ?_⟩
        change (C.boundaryEndEquiv retain (cycle.point i)).1 = bank
        rw [← same]
        exact congrArg Prod.fst ((C.boundaryEndEquiv retain).apply_symm_apply (bank, false))
      · refine ⟨i, ?_⟩
        have equal := (C.boundaryEnd_bank_eq_iff retain p (cycle.point i)).mpr (Or.inr same)
        exact equal.symm.trans (congrArg Prod.fst
          ((C.boundaryEndEquiv retain).apply_symm_apply (bank, false)))⟩

/-- A covering closed cycle enumerates each actual boundary vertex copy exactly once. -/
def boundaryCycleVertexEquiv : Fin (n + 1) ≃ C.BoundaryVertex retain :=
  Equiv.ofBijective (fun i => C.boundaryEndAsVertex retain (cycle.point i)) ⟨by
    intro i j same
    exact C.boundaryCycle_vertices_injective retain cycle closes (congrArg Subtype.val same), by
      intro vertex
      obtain ⟨germ, fixed⟩ :=
        (C.isBoundaryVertex_iff_linkMate_fixed retain vertex.val).mp vertex.property
      have boundary : C.IsBoundaryEdge retain (C.germEdge germ.val) :=
        (C.mateGerm_eq_self_iff retain germ.val).mp (congrArg Subtype.val fixed)
      let p : C.BoundaryEnd retain := ⟨germ.val, boundary⟩
      have apex : C.boundaryEndAsVertex retain p = vertex := Subtype.ext germ.property
      obtain ⟨i, same | same⟩ := covers p
      · refine ⟨i, ?_⟩
        change C.boundaryEndAsVertex retain (cycle.point i) = vertex
        rw [← same]
        exact apex
      · refine ⟨finRotate (n + 1) i, ?_⟩
        change C.boundaryEndAsVertex retain (cycle.point (finRotate (n + 1) i)) = vertex
        rw [← C.boundaryCycle_next_vertex retain cycle closes]
        change p = C.boundaryTurn retain (cycle.point i) at same
        rw [← same]
        exact apex⟩

include cycle closes covers in
/-- In particular a connected actual boundary has equally many banks and vertices. -/
theorem boundaryCycle_card_vertices_eq_banks :
    Nat.card (C.BoundaryVertex retain) = Nat.card (C.BoundaryBank retain) := by
  exact (Nat.card_congr (C.boundaryCycleVertexEquiv retain cycle closes covers)).symm.trans
    (Nat.card_congr (C.boundaryCycleBankEquiv retain cycle covers))

/-- If all vertices are boundary copies, the cycle enumerates all of them. -/
def boundaryCycleAllVertexEquiv (all_boundary : ∀ v, C.IsBoundaryVertex retain v) :
    Fin (n + 1) ≃ C.Vertex retain :=
  (C.boundaryCycleVertexEquiv retain cycle closes covers).trans
    (Equiv.subtypeUnivEquiv all_boundary)

include closes covers in
theorem sum_boundaryCycle_vertices (all_boundary : ∀ v, C.IsBoundaryVertex retain v)
    (weight : C.Vertex retain → ℝ) :
    (∑ i, weight (C.boundaryEndVertex retain (cycle.point i))) = ∑ v, weight v :=
  (C.boundaryCycleAllVertexEquiv retain cycle closes covers all_boundary).sum_comp weight

/-- Connectedness of the actual bank graph supplies a covering closed boundary order. -/
theorem exists_boundaryCycle_cover_of_connected
    (connected : (C.boundaryGraph retain).adjacencyGraph.Connected) :
    ∃ n, ∃ cycle : (C.boundarySystem retain).Chain n,
      C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first ∧
        ∀ p, cycle.Visited p := by
  obtain ⟨v⟩ := connected.nonempty
  obtain ⟨bank, _w, _link⟩ := C.boundaryGraph_vertex_incident retain v
  let p := (C.boundaryEndEquiv retain).symm (bank, false)
  obtain ⟨n, c, _first, closed⟩ := C.exists_boundaryCycle retain p
  exact ⟨n, c, closed, C.boundaryCycle_covers_of_connected retain c closed connected⟩

end Unfoldings.TriangleComplex
