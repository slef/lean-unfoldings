module

public import Unfoldings.Development.IntervalRays
public import Unfoldings.Complex.BoundaryCycleEnumeration

/-!
# Consistent orientation along actual developed boundary banks

Developed corner orientation reverses at either endpoint involution: exchanging
the ends of one bank, or exchanging the two banks at one boundary vertex copy.
Thus the actual boundary cycle has one consistent orientation even if its
planar image overlaps itself.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- The signed developed corner area, starting along the specified raw edge germ. -/
def germOrientation (p : C.Germ) : ℝ :=
  orient (D.place p.1.1 ((C.triangle p.1.1).vertex p.1.2))
    (D.germFarPoint p) (D.germFarPoint (C.turnGerm p))

theorem germOrientation_eq {w : C.Vertex retain} (p : C.LinkGerm retain w) :
    D.germOrientation p.val = orient 0 (D.germRay p) (D.germRay (C.linkTurn retain w p)) := by
  rw [germOrientation, germRay, germRay, ← D.linkGerm_apex p]
  simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
  rfl

theorem germOrientation_ne_zero (p : C.Germ) : D.germOrientation p ≠ 0 := by
  rw [D.germOrientation_eq (⟨p, rfl⟩ : C.LinkGerm retain (C.vertexOfCorner retain p.1))]
  exact D.germRay_orient_ne_zero _

@[simp] theorem germOrientation_turn (p : C.Germ) :
    D.germOrientation (C.turnGerm p) = -D.germOrientation p := by
  change orient (D.place p.1.1 ((C.triangle p.1.1).vertex p.1.2))
    (D.germFarPoint (C.turnGerm p))
    (D.germFarPoint (C.turnGerm (C.turnGerm p))) = _
  rw [C.turnGerm_involutive]
  simp only [germOrientation, orient]
  ring

/-- Along an actual bank, reversing the bank direction reverses corner orientation. -/
theorem germOrientation_bank_end (edge : EdgeRef Face) (b : Bool) :
    D.germOrientation (C.germOfEndpoint edge (!b)) =
      -D.germOrientation (C.germOfEndpoint edge b) := by
  obtain ⟨f, i⟩ := edge
  cases b <;> fin_cases i <;>
    simp [germOrientation, germFarPoint, TriangleComplex.germOfEndpoint,
      TriangleComplex.germFarCorner, TriangleComplex.turnGerm, Triangle.next, orient] <;> ring

theorem germOrientation_boundaryTurn (p : C.BoundaryEnd retain) :
    D.germOrientation (C.boundaryTurn retain p).val = -D.germOrientation p.val := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
  change D.germOrientation (C.germOfEndpoint bank.val (!b)) =
    -D.germOrientation (C.germOfEndpoint bank.val b)
  exact D.germOrientation_bank_end bank.val b

/-- The corners of any actual developed link interval have the same orientation sign. -/
theorem link_germOrientation_sign {w : C.Vertex retain} {n : ℕ}
    (c : (C.linkSystem retain w).Chain n) (i : Fin (n + 1)) :
    (0 < D.germOrientation (c.point i).val) ↔ 0 < D.germOrientation c.first.val := by
  have signs := interval_cone_orient_sign_of_adjacent (D.intervalLinkRay c)
    (D.intervalLinkRay_genuine c) (D.intervalLinkRay_adjacent c) i
  change (0 < D.germOrientation (c.point i).val) ↔ 0 < D.germOrientation (c.point 0).val
  simpa only [D.intervalLinkRay_castSucc, D.intervalLinkRay_succ, ← D.germOrientation_eq]
    using signs

/-- At one boundary copy, passing through its full actual corner star reverses the sign. -/
theorem germOrientation_boundaryMate (p : C.BoundaryEnd retain) :
    (0 < D.germOrientation (C.boundaryMate retain p).val) ↔ D.germOrientation p.val < 0 := by
  let w := C.boundaryEndVertex retain p
  let start : C.LinkGerm retain w := ⟨p.val, rfl⟩
  have fixed : C.linkMate retain w start = start :=
    Subtype.ext ((C.mateGerm_eq_self_iff retain p.val).mpr p.property)
  obtain ⟨n, c, first, finish, _covers⟩ := (C.linkSystem retain w).exists_interval_chain
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
  have ending : D.germOrientation (C.boundaryMate retain p).val =
      -D.germOrientation c.last.val := by
    rw [← other]
    exact D.germOrientation_turn c.last.val
  have signs := D.link_germOrientation_sign c (Fin.last n)
  change (0 < D.germOrientation c.last.val) ↔ 0 < D.germOrientation c.first.val at signs
  rw [first] at signs
  change (0 < D.germOrientation c.last.val) ↔ 0 < D.germOrientation p.val at signs
  rw [ending]
  have initial_ne := D.germOrientation_ne_zero p.val
  have last_ne := D.germOrientation_ne_zero c.last.val
  constructor
  · intro negative
    by_contra nonnegative
    have positive : 0 < D.germOrientation p.val := by
      rcases lt_or_gt_of_ne initial_ne with below | above
      · exact (nonnegative below).elim
      · exact above
    have := signs.mpr positive
    linarith
  · intro negative
    by_contra nonnegative
    have positive : 0 < D.germOrientation c.last.val := by
      rcases lt_or_gt_of_ne last_ne with below | above
      · linarith
      · exact above
    have := signs.mp positive
    linarith

/-- One boundary step preserves the developed orientation sign. -/
theorem germOrientation_boundary_next (p : C.BoundaryEnd retain) :
    (0 < D.germOrientation (C.boundaryMate retain (C.boundaryTurn retain p)).val) ↔
      0 < D.germOrientation p.val := by
  rw [D.germOrientation_boundaryMate, D.germOrientation_boundaryTurn]
  exact neg_neg_iff_pos

/-- Every bank in the actual cycle uses the same developed orientation. -/
theorem boundaryCycle_orientation {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (i : Fin (n + 1)) :
    (0 < D.germOrientation (cycle.point i).val) ↔ 0 < D.germOrientation cycle.first.val := by
  refine Fin.induction Iff.rfl (fun k previous => ?_) i
  have step := D.germOrientation_boundary_next (cycle.point k.castSucc)
  have next := cycle.next k
  change C.boundaryMate retain (C.boundaryTurn retain (cycle.point k.castSucc)) =
    cycle.point k.succ at next
  rw [next] at step
  exact step.trans previous

end Unfoldings.FacewiseDevelopment
