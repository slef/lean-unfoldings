module

public import Unfoldings.Complex.ContourBetweenChildBlocks
public import Unfoldings.Topology.FiniteIntervalCover

/-! Enumerate all final roof wedges in a contour interval and the child seams between them. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

local notation "Retain" => C.selectedRetain S
local notation "Visit[" j "]" => C.contourOriginalVertex S Q j
local notation "Copy[" j "]" => C.boundaryEndVertex Retain (Q.cycle.point j)
local notation "Interval[" v "," h "]" => C.contourParentInterval S Q roots starts v h
local notation "ParentBank[" v "," h "," side "]" => C.contourParentBank S Q roots starts v h side

local notation "Edge" => {v : C.Vertex Set.univ // v ∉ P.roots}

/-- A nonempty interval of visits to one nonroot vertex, in literal contour order. -/
structure ContourParentWedgeRun (parent : C.Vertex Set.univ) (first last : Fin (Q.length + 1)) where
  length : ℕ
  visit : Fin (length + 1) ↪o Fin (Q.length + 1)
  at_first : visit 0 = first
  at_last : visit (Fin.last length) = last
  visits (j : Fin (Q.length + 1)) :
    (∃ i, visit i = j) ↔ Visit[j] = parent ∧ first ≤ j ∧ j ≤ last
  child : Fin length → Edge
  child_parent (i : Fin length) : P.parent (child i).val = parent
  enters (i : Fin length) : (Interval[(child i).val,(child i).property]).enter = visit i.castSucc
  returns (i : Fin length) :
    finRotate (Q.length + 1) (Interval[(child i).val,(child i).property]).leave = visit i.succ

/-- All child seams between the two visits are found by sorting precisely the
parent's intervening contour indices. -/
def contourParentWedgeRun (parent : C.Vertex Set.univ) (nonroot : parent ∉ P.roots)
    (first last : Fin (Q.length + 1)) (ordered : first ≤ last)
    (first_parent : Visit[first] = parent) (last_parent : Visit[last] = parent) :
    C.ContourParentWedgeRun S Q roots starts parent first last := Classical.choice (by
  classical
  let s := Finset.univ.filter (fun j : Fin (Q.length + 1) =>
    Visit[j] = parent ∧ first ≤ j ∧ j ≤ last)
  have mem_first : first ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, first_parent,
    le_rfl, ordered⟩
  have mem_last : last ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, last_parent,
    ordered, le_rfl⟩
  let n := s.card - 1
  have cardinality : s.card = n + 1 := by
    have h := Finset.card_pos.mpr ⟨first, mem_first⟩
    omega
  let f := s.orderEmbOfFin cardinality
  have names (j : Fin (Q.length + 1)) :
      (∃ i, f i = j) ↔ Visit[j] = parent ∧ first ≤ j ∧ j ≤ last := by
    change j ∈ Set.range f ↔ _
    rw [s.range_orderEmbOfFin cardinality]
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  have at_index (i : Fin (n + 1)) : Visit[f i] = parent ∧ first ≤ f i ∧ f i ≤ last :=
    (names (f i)).mp ⟨i, rfl⟩
  have starts_at : f 0 = first := by
    obtain ⟨i, h⟩ := (names first).mpr ⟨first_parent, le_rfl, ordered⟩
    exact le_antisymm ((f.monotone (Fin.zero_le i)).trans_eq h) (at_index 0).2.1
  have ends_at : f (Fin.last n) = last := by
    obtain ⟨i, h⟩ := (names last).mpr ⟨last_parent, ordered, le_rfl⟩
    exact le_antisymm (at_index (Fin.last n)).2.2 (h.symm.trans_le (f.monotone (Fin.le_last i)))
  have successive (i : Fin n) : ∃ e : Edge, P.parent e.val = parent ∧
      (Interval[e.val,e.property]).enter = f i.castSucc ∧
      finRotate (Q.length + 1) (Interval[e.val,e.property]).leave = f i.succ := by
    obtain ⟨child, child_nonroot, parent_eq, enter, back⟩ :=
      C.exists_child_of_consecutive_contour_visits S Q roots starts parent nonroot
        (f i.castSucc) (f i.succ) (f.strictMono Fin.castSucc_lt_succ)
        (at_index _).1 (at_index _).1 (by
          intro j earlier later parent_eq
          have first_bound : first ≤ j := (at_index i.castSucc).2.1.trans earlier.le
          have last_bound : j ≤ last := later.le.trans (at_index i.succ).2.2
          exact orderEmbOfFin_no_between s cardinality i
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, parent_eq, first_bound, last_bound⟩)
            ⟨earlier, later⟩)
    exact ⟨⟨child, child_nonroot⟩, parent_eq, enter, back⟩
  choose child same enters returns using successive
  exact ⟨⟨n, f, starts_at, ends_at, names, child, same, enters, returns⟩⟩)

namespace ContourParentWedgeRun

variable {C S Q roots starts} {parent : C.Vertex Set.univ} {first last : Fin (Q.length + 1)}
  (A : C.ContourParentWedgeRun S Q roots starts parent first last)

theorem at_visit (i : Fin (A.length + 1)) :
    Visit[A.visit i] = parent ∧ first ≤ A.visit i ∧ A.visit i ≤ last :=
  (A.visits _).mp ⟨i, rfl⟩

/-- The child on the preceding side of each wedge, including the exterior endpoint. -/
def previous (old_child : Edge) (i : Fin (A.length + 1)) : Edge :=
  Fin.cases old_child A.child i

/-- The child on the following side of each wedge, including the exterior endpoint. -/
def following (new_child : Edge) (i : Fin (A.length + 1)) : Edge :=
  Fin.lastCases new_child A.child i

@[simp] theorem following_last (new_child : Edge) :
    A.following new_child (Fin.last A.length) = new_child := Fin.lastCases_last

@[simp] theorem following_castSucc (new_child : Edge) (i : Fin A.length) :
    A.following new_child i.castSucc = A.child i := Fin.lastCases_castSucc i

theorem previous_returns (old_child : Edge)
    (after_old : finRotate (Q.length + 1) (Interval[old_child.val,old_child.property]).leave = first)
    (i : Fin (A.length + 1)) :
    let edge := A.previous old_child i
    finRotate (Q.length + 1) (Interval[edge.val,edge.property]).leave = A.visit i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact after_old.trans A.at_first.symm
  · exact A.returns j

theorem following_enters (new_child : Edge)
    (before_new : (Interval[new_child.val,new_child.property]).enter = last)
    (i : Fin (A.length + 1)) :
    let edge := A.following new_child i
    (Interval[edge.val,edge.property]).enter = A.visit i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (A.following_last new_child).symm ▸ (before_new.trans A.at_last.symm)
  · exact (A.following_castSucc new_child j).symm ▸ A.enters j

end ContourParentWedgeRun

end Unfoldings.TriangleComplex
