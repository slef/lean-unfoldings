module

public import Unfoldings.Development.Subdivision
public import Mathlib.Topology.Baire.Lemmas

/-! Nonoverlap is invariant under conforming subdivision, in both directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (E : FacewiseDevelopment C retain) (S : C.Subdivision D)
  (H : S.Conforming retain fineRetain)

theorem child_cover (f : Face) {p : Plane} (member : p ∈ E.faceImage f) :
    ∃ g, S.parent g = f ∧ p ∈ (E.subdivide S H).faceImage g := by
  obtain ⟨q, hq, rfl⟩ := member
  obtain ⟨g, x, parent, point⟩ := S.cover f ⟨q, hq⟩
  refine ⟨g, parent, x.val, x.property, ?_⟩
  change E.place (S.parent g) (S.place g x.val) = E.place f q
  rw [parent, point]

/-- Subdivision cannot hide an open overlap inside the new edge skeleton. -/
theorem nonoverlapping_of_subdivide (fine : (E.subdivide S H).Nonoverlapping) :
    E.Nonoverlapping := by
  intro f g different
  apply Set.disjoint_left.mpr
  intro p first last
  let A := E.subdivide S H
  have closed (k : Child) : IsClosed (A.faceImage k) :=
    ((D.triangle k).compact_carrier.image (A.place k).continuous).isClosed
  have dense : Dense (⋂ k : Child, (frontier (A.faceImage k))ᶜ) := by
    apply dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
    intro k x
    rw [closure_compl, interior_frontier (closed k)]
    simp
  obtain ⟨q, off, overlap⟩ := dense.exists_mem_open
    (isOpen_interior.inter isOpen_interior) ⟨p, first, last⟩
  obtain ⟨a, parent_a, inside_a⟩ := E.child_cover S H f (interior_subset overlap.1)
  obtain ⟨b, parent_b, inside_b⟩ := E.child_cover S H g (interior_subset overlap.2)
  have distinct : a ≠ b := by
    intro equal
    exact different (parent_a.symm.trans ((congrArg S.parent equal).trans parent_b))
  have qa : q ∈ interior (A.faceImage a) :=
    (mem_interior_iff_notMem_frontier inside_a).mpr (Set.mem_iInter.mp off a)
  have qb : q ∈ interior (A.faceImage b) :=
    (mem_interior_iff_notMem_frontier inside_b).mpr (Set.mem_iInter.mp off b)
  exact Set.disjoint_left.mp (fine a b distinct) qa qb

theorem subdivide_nonoverlapping_iff : (E.subdivide S H).Nonoverlapping ↔ E.Nonoverlapping :=
  ⟨E.nonoverlapping_of_subdivide S H, fun nonoverlap => Nonoverlapping.subdivide E S H nonoverlap⟩

end Unfoldings.FacewiseDevelopment
