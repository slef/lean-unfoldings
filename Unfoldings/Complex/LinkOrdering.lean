module

public import Unfoldings.Complex.LinkConnectivity
public import Unfoldings.Complex.Angles
public import Unfoldings.Topology.PairedInvolutions

/-!
# Constructed cyclic and interval orders of vertex links

The link order is derived from the actual seam pairings. Each original corner
appears once, its two germs appear as its two endpoints, and the ordered corner
angles sum to the previously defined total angle of the metric vertex.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The generic paired-interval system supplied by the actual vertex link. -/
def linkSystem (retain : Set C.Seam) (v : C.Vertex retain) :
    PairedInvolutions.System (C.LinkGerm retain v) where
  turn := C.linkTurn retain v
  mate := C.linkMate retain v
  turn_involutive := C.linkTurn_involutive retain v
  mate_involutive := C.linkMate_involutive retain v
  turn_ne := C.linkTurn_ne retain v

theorem linkSystem_connected (retain : Set C.Seam) (v : C.Vertex retain) :
    (C.linkSystem retain v).Connected := C.linkGerms_related retain v

/-- Every interior vertex has a cyclic link order, including a one-corner loop. -/
theorem exists_cyclic_link (retain : Set C.Seam) (v : C.Vertex retain)
    (interior : ¬ C.IsBoundaryVertex retain v) :
    ∃ n, ∃ c : (C.linkSystem retain v).Chain n,
      C.linkMate retain v (C.linkTurn retain v c.last) = c.first ∧ ∀ p, c.Visited p := by
  have free (p : C.LinkGerm retain v) : C.linkMate retain v p ≠ p := fun fixed =>
    interior ((C.isBoundaryVertex_iff_linkMate_fixed retain v).mpr ⟨p, fixed⟩)
  obtain ⟨p⟩ := C.nonempty_linkGerm retain v
  obtain ⟨n, c, first, closes, covers⟩ := (C.linkSystem retain v).exists_cycle_chain
    (C.linkSystem_connected retain v) free p
  exact ⟨n, c, closes, covers⟩

/-- Every boundary vertex has an interval link order with both terminal germs unpaired. -/
theorem exists_interval_link (retain : Set C.Seam) (v : C.Vertex retain)
    (boundary : C.IsBoundaryVertex retain v) :
    ∃ n, ∃ c : (C.linkSystem retain v).Chain n,
      C.linkMate retain v c.first = c.first ∧
      C.linkMate retain v (C.linkTurn retain v c.last) = C.linkTurn retain v c.last ∧
      ∀ p, c.Visited p := by
  obtain ⟨p, fixed⟩ := (C.isBoundaryVertex_iff_linkMate_fixed retain v).mp boundary
  obtain ⟨n, c, first, finish, covers⟩ := (C.linkSystem retain v).exists_interval_chain
    (C.linkSystem_connected retain v) p fixed
  refine ⟨n, c, ?_, finish, covers⟩
  rw [first, fixed]

/-- A boundary vertex has precisely two boundary germs, even if they belong to the same bank. -/
theorem boundary_link_two_fixed (retain : Set C.Seam) (v : C.Vertex retain)
    (boundary : C.IsBoundaryVertex retain v) : ∃ p q : C.LinkGerm retain v,
      p ≠ q ∧ ∀ r, C.linkMate retain v r = r ↔ r = p ∨ r = q := by
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link retain v boundary
  exact ⟨c.first, C.linkTurn retain v c.last, c.disjoint 0 (Fin.last n),
    c.mate_fixed_iff start finish covers⟩

/-- The original tagged corners that contribute to one retained vertex copy. -/
def CornerAt (retain : Set C.Seam) (v : C.Vertex retain) :=
  {c : C.Corner // C.vertexOfCorner retain c = v}

instance (retain : Set C.Seam) (v : C.Vertex retain) : Finite (C.CornerAt retain v) :=
  inferInstanceAs (Finite {c : C.Corner // C.vertexOfCorner retain c = v})

instance (retain : Set C.Seam) (v : C.Vertex retain) : Fintype (C.CornerAt retain v) :=
  Fintype.ofFinite _

theorem totalAngle_eq_sum_cornerAt (retain : Set C.Seam) (v : C.Vertex retain) :
    C.totalAngle retain v =
      ∑ c : C.CornerAt retain v, (C.triangle c.val.1).cornerAngle c.val.2 := by
  classical
  exact (Finset.sum_filter _ _).symm.trans
    (Finset.sum_subtype (Finset.univ.filter (fun c => C.vertexOfCorner retain c = v))
      (by simp) (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2))

/-- An ordered link chain lists each incident corner exactly once. -/
def linkCornerEquiv (retain : Set C.Seam) (v : C.Vertex retain) {n : ℕ}
    (c : (C.linkSystem retain v).Chain n) (covers : ∀ p, c.Visited p) :
    Fin (n + 1) ≃ C.CornerAt retain v := by
  let corner (i : Fin (n + 1)) : C.CornerAt retain v := ⟨(c.point i).val.1, (c.point i).property⟩
  have injective : Function.Injective corner := by
    intro i j equal
    have same : (c.point i).val.1 = (c.point j).val.1 := congrArg Subtype.val equal
    rcases (C.germ_corner_eq_iff _ _).mp same with same | opposite
    · exact c.injective (Subtype.ext same)
    · exact (c.disjoint i j (Subtype.ext opposite)).elim
  have surjective : Function.Surjective corner := by
    intro a
    let p : C.LinkGerm retain v := ⟨(a.val, false), a.property⟩
    obtain ⟨i, same | opposite⟩ := covers p
    · exact ⟨i, Subtype.ext (congrArg (fun q : C.LinkGerm retain v => q.val.1) same).symm⟩
    · exact ⟨i, Subtype.ext (congrArg (fun q : C.LinkGerm retain v => q.val.1) opposite).symm⟩
  exact Equiv.ofBijective corner ⟨injective, surjective⟩

theorem sum_linkCornerAngle (retain : Set C.Seam) (v : C.Vertex retain) {n : ℕ}
    (c : (C.linkSystem retain v).Chain n) (covers : ∀ p, c.Visited p) :
    (∑ i : Fin (n + 1),
      (C.triangle ((C.linkCornerEquiv retain v c covers) i).val.1).cornerAngle
        ((C.linkCornerEquiv retain v c covers) i).val.2) = C.totalAngle retain v := by
  exact ((C.linkCornerEquiv retain v c covers).sum_comp
    (fun a : C.CornerAt retain v => (C.triangle a.val.1).cornerAngle a.val.2)).trans
      (C.totalAngle_eq_sum_cornerAt retain v).symm

end Unfoldings.TriangleComplex
