module

public import Unfoldings.Complex.LinkOrdering

/-!
# Finite cyclic orders of actual cut banks

Boundary ends are the unpaired original corner germs. Exactly two such germs
belong to each boundary vertex copy, so the other end at that vertex is a
fixed-point-free involution. Together with exchange of a bank's endpoints it
supplies a finite system of closed bank cycles, without disk assumptions.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

abbrev BoundaryEnd := {p : C.Germ // C.IsBoundaryEdge retain (C.germEdge p)}

def boundaryEndVertex (p : C.BoundaryEnd retain) : C.Vertex retain :=
  C.vertexOfCorner retain p.val.1

def boundaryEndEquiv : C.BoundaryEnd retain ≃ C.BoundaryBank retain × Bool where
  toFun p := (⟨C.germEdge p.val, p.property⟩, p.val.2)
  invFun p := ⟨C.germOfEndpoint p.1.val p.2, by
    rw [C.germEdge_germOfEndpoint]
    exact p.1.property⟩
  left_inv p := Subtype.ext (C.germOfEndpoint_germEdge p.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (C.germEdge_germOfEndpoint _ _)
    · rfl

def boundaryTurn (p : C.BoundaryEnd retain) : C.BoundaryEnd retain :=
  (C.boundaryEndEquiv retain).symm ((C.boundaryEndEquiv retain p).1,
    !(C.boundaryEndEquiv retain p).2)

theorem boundaryTurn_involutive : Function.Involutive (C.boundaryTurn retain) := by
  intro p
  apply (C.boundaryEndEquiv retain).injective
  simp [boundaryTurn]

theorem boundaryTurn_ne (p : C.BoundaryEnd retain) : C.boundaryTurn retain p ≠ p := by
  intro equal
  have flags := congrArg (fun q => (C.boundaryEndEquiv retain q).2) equal
  simp only [boundaryTurn, Equiv.apply_symm_apply, Bool.not_eq_self] at flags

/-- Every retained boundary vertex copy has precisely two bank ends. -/
theorem boundaryEnd_two_at_vertex (p : C.BoundaryEnd retain) :
    ∃ a b : C.BoundaryEnd retain, a ≠ b ∧
      ∀ q, C.boundaryEndVertex retain q = C.boundaryEndVertex retain p ↔ q = a ∨ q = b := by
  let vertex := C.boundaryEndVertex retain p
  let germ : C.LinkGerm retain vertex := ⟨p.val, rfl⟩
  have fixed : C.linkMate retain vertex germ = germ :=
    Subtype.ext ((C.mateGerm_eq_self_iff retain p.val).mpr p.property)
  have boundary := (C.isBoundaryVertex_iff_linkMate_fixed retain vertex).mpr ⟨germ, fixed⟩
  obtain ⟨a, b, different, two⟩ := C.boundary_link_two_fixed retain vertex boundary
  have boundary_a : C.IsBoundaryEdge retain (C.germEdge a.val) :=
    (C.mateGerm_eq_self_iff retain a.val).mp
      (congrArg Subtype.val ((two a).mpr (Or.inl rfl)))
  have boundary_b : C.IsBoundaryEdge retain (C.germEdge b.val) :=
    (C.mateGerm_eq_self_iff retain b.val).mp
      (congrArg Subtype.val ((two b).mpr (Or.inr rfl)))
  let first : C.BoundaryEnd retain := ⟨a.val, boundary_a⟩
  let second : C.BoundaryEnd retain := ⟨b.val, boundary_b⟩
  refine ⟨first, second, ?_, ?_⟩
  · intro same
    apply different
    apply Subtype.ext
    exact congrArg (fun q : C.BoundaryEnd retain => q.val) same
  · intro q
    constructor
    · intro same_vertex
      let q' : C.LinkGerm retain vertex := ⟨q.val, same_vertex⟩
      have q_fixed : C.linkMate retain vertex q' = q' :=
        Subtype.ext ((C.mateGerm_eq_self_iff retain q.val).mpr q.property)
      rcases (two q').mp q_fixed with same | same
      · left
        apply Subtype.ext
        exact congrArg (fun r : C.LinkGerm retain vertex => r.val) same
      · right
        apply Subtype.ext
        exact congrArg (fun r : C.LinkGerm retain vertex => r.val) same
    · rintro (rfl | rfl)
      · exact a.property
      · exact b.property

theorem exists_unique_other_boundaryEnd (p : C.BoundaryEnd retain) :
    ∃! q : C.BoundaryEnd retain, q ≠ p ∧
      C.boundaryEndVertex retain q = C.boundaryEndVertex retain p := by
  obtain ⟨a, b, different, two⟩ := C.boundaryEnd_two_at_vertex retain p
  rcases (two p).mp rfl with rfl | rfl
  · refine ⟨b, ⟨different.symm, (two b).mpr (Or.inr rfl)⟩, ?_⟩
    intro q hq
    rcases (two q).mp hq.2 with same | same
    · exact (hq.1 same).elim
    · exact same
  · refine ⟨a, ⟨different, (two a).mpr (Or.inl rfl)⟩, ?_⟩
    intro q hq
    rcases (two q).mp hq.2 with same | same
    · exact same
    · exact (hq.1 same).elim

def boundaryMate (p : C.BoundaryEnd retain) : C.BoundaryEnd retain :=
  Classical.choose (C.exists_unique_other_boundaryEnd retain p).exists

theorem boundaryMate_spec (p : C.BoundaryEnd retain) : C.boundaryMate retain p ≠ p ∧
    C.boundaryEndVertex retain (C.boundaryMate retain p) = C.boundaryEndVertex retain p :=
  Classical.choose_spec (C.exists_unique_other_boundaryEnd retain p).exists

theorem boundaryMate_involutive : Function.Involutive (C.boundaryMate retain) := by
  intro p
  exact (C.exists_unique_other_boundaryEnd retain (C.boundaryMate retain p)).unique
    (C.boundaryMate_spec retain _) ⟨(C.boundaryMate_spec retain p).1.symm,
      (C.boundaryMate_spec retain p).2.symm⟩

def boundarySystem : PairedInvolutions.System (C.BoundaryEnd retain) where
  turn := C.boundaryTurn retain
  mate := C.boundaryMate retain
  turn_involutive := C.boundaryTurn_involutive retain
  mate_involutive := C.boundaryMate_involutive retain
  turn_ne := C.boundaryTurn_ne retain

/-- Every bank end starts a closed bank cycle, even on disconnected cut surfaces. -/
theorem exists_boundaryCycle (p : C.BoundaryEnd retain) :
    ∃ n, ∃ cycle : (C.boundarySystem retain).Chain n,
      cycle.first = p ∧
        C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first := by
  obtain ⟨n, cycle, first, inside⟩ := (C.boundarySystem retain).exists_closed_chain p
  rcases cycle.closes_or_boundary inside with closes | boundary
  · exact ⟨n, cycle, first, closes⟩
  · exact ((C.boundaryMate_spec retain _).1 boundary).elim

theorem boundaryEnd_bank_eq_iff (p q : C.BoundaryEnd retain) :
    (C.boundaryEndEquiv retain p).1 = (C.boundaryEndEquiv retain q).1 ↔
      p = q ∨ p = C.boundaryTurn retain q := by
  constructor
  · intro same_bank
    have flags : (C.boundaryEndEquiv retain p).2 = (C.boundaryEndEquiv retain q).2 ∨
        (C.boundaryEndEquiv retain p).2 = !(C.boundaryEndEquiv retain q).2 := by
      cases (C.boundaryEndEquiv retain p).2 <;>
        cases (C.boundaryEndEquiv retain q).2 <;> simp
    rcases flags with same | opposite
    · exact Or.inl ((C.boundaryEndEquiv retain).injective (Prod.ext same_bank same))
    · right
      apply (C.boundaryEndEquiv retain).injective
      have pairs : C.boundaryEndEquiv retain p =
          ((C.boundaryEndEquiv retain q).1, !(C.boundaryEndEquiv retain q).2) :=
        Prod.ext same_bank opposite
      simpa only [boundaryTurn, Equiv.apply_symm_apply] using pairs
  · rintro (rfl | rfl)
    · rfl
    · simp [boundaryTurn]

theorem boundaryEnd_vertex_eq_iff (p q : C.BoundaryEnd retain) :
    C.boundaryEndVertex retain p = C.boundaryEndVertex retain q ↔
      p = q ∨ p = C.boundaryMate retain q := by
  constructor
  · intro same_vertex
    by_cases same : p = q
    · exact Or.inl same
    · exact Or.inr ((C.exists_unique_other_boundaryEnd retain q).unique
        ⟨same, same_vertex⟩ (C.boundaryMate_spec retain q))
  · rintro (rfl | rfl)
    · rfl
    · exact (C.boundaryMate_spec retain q).2

theorem boundaryChain_banks_injective {n : ℕ} (chain : (C.boundarySystem retain).Chain n) :
    Function.Injective (fun i => (C.boundaryEndEquiv retain (chain.point i)).1) := by
  intro i j same
  rcases (C.boundaryEnd_bank_eq_iff retain _ _).mp same with equal | opposite
  · exact chain.injective equal
  · exact (chain.disjoint i j opposite).elim

theorem boundaryCycle_vertices_injective {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (closes : C.boundaryMate retain (C.boundaryTurn retain cycle.last) = cycle.first) :
    Function.Injective (fun i => C.boundaryEndVertex retain (cycle.point i)) := by
  intro i j same
  rcases (C.boundaryEnd_vertex_eq_iff retain _ _).mp same with equal | opposite
  · exact cycle.injective equal
  · exfalso
    have start : C.boundaryMate retain cycle.first = C.boundaryTurn retain cycle.last := by
      rw [← closes, C.boundaryMate_involutive]
    revert opposite
    refine Fin.cases ?_ (fun k => ?_) j
    · intro opposite
      rw [show cycle.point 0 = cycle.first from rfl, start] at opposite
      exact cycle.disjoint i (Fin.last n) opposite
    · intro opposite
      have previous := cycle.mate_succ k
      change C.boundaryMate retain (cycle.point k.succ) = C.boundaryTurn retain
        (cycle.point k.castSucc) at previous
      rw [previous] at opposite
      exact cycle.disjoint i k.castSucc opposite

end Unfoldings.TriangleComplex
