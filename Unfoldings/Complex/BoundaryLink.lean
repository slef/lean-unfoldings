module

public import Unfoldings.Complex.BoundaryOrdering

/-! The actual ordered corner interval between the two banks at a boundary copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face) (retain : Set C.Seam)

/-- Start at a specified actual bank; the other end is the actual boundary-mate bank. -/
theorem exists_boundary_link (p : C.BoundaryEnd retain) :
    ∃ n, ∃ c : (C.linkSystem retain (C.boundaryEndVertex retain p)).Chain n,
      c.first.val = p.val ∧
      (C.linkTurn retain (C.boundaryEndVertex retain p) c.last).val =
        (C.boundaryMate retain p).val ∧ (∀ r, c.Visited r) := by
  let w := C.boundaryEndVertex retain p
  let start : C.LinkGerm retain w := ⟨p.val, rfl⟩
  have fixed : C.linkMate retain w start = start :=
    Subtype.ext ((C.mateGerm_eq_self_iff retain p.val).mpr p.property)
  obtain ⟨n, c, first, finish, covers⟩ := (C.linkSystem retain w).exists_interval_chain
    (C.linkSystem_connected retain w) start fixed
  let last := C.linkTurn retain w c.last
  have unpaired : C.IsBoundaryEdge retain (C.germEdge last.val) :=
    (C.mateGerm_eq_self_iff retain last.val).mp (congrArg Subtype.val finish)
  let q : C.BoundaryEnd retain := ⟨last.val, unpaired⟩
  have different : q ≠ p := by
    intro same
    have raw : last.val = c.first.val :=
      (congrArg Subtype.val same).trans (congrArg Subtype.val first).symm
    exact c.disjoint 0 (Fin.last n) (Subtype.ext raw.symm)
  have same_vertex : C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := last.property
  have other : q = C.boundaryMate retain p :=
    (C.exists_unique_other_boundaryEnd retain p).unique ⟨different, same_vertex⟩
      (C.boundaryMate_spec retain p)
  exact ⟨n, c, congrArg Subtype.val first, congrArg Subtype.val other, covers⟩

end Unfoldings.TriangleComplex
