module

public import Unfoldings.Cap.BranchDisplacements
public import Unfoldings.Complex.BoundaryEndDistinct

/-! An original rim-root subtree has exactly the two original rim banks as contour exits. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Among original roots, only a root itself belongs to its descendant subtree. -/
theorem root_descendant_iff {e w : C.Vertex Set.univ} (root : w ∈ M.parents.roots) :
    M.parents.Ancestor w e ↔ w = e := by
  constructor
  · rintro ⟨n, reaches⟩
    exact (Function.iterate_fixed (M.parents.fixed_root w root) n).symm.trans reaches
  · rintro rfl
    exact M.parents.ancestor_refl _

/-- A root subtree is crossed only by the original rim banks incident to that root. -/
theorem root_subtreeCrossingBank_iff (e : C.Vertex Set.univ) (root : e ∈ M.parents.roots)
    (bank : C.BoundaryBank M.retain) :
    C.SubtreeCrossingBank M.selection e bank ↔
      ∃ p : C.BoundaryEnd Set.univ, C.boundaryEndVertex Set.univ p = e ∧
        bank = C.oldBoundaryBank (Set.subset_univ _) (C.boundaryEndEquiv Set.univ p).1 := by
  rcases C.relativeBank_cases M.retain Set.univ bank with old | ⟨s, side, rfl⟩
  · let b : C.BoundaryBank Set.univ := ⟨bank.val, old⟩
    let p := (C.boundaryEndEquiv Set.univ).symm (b, false)
    let q := C.boundaryTurn Set.univ p
    have p_root : C.boundaryEndVertex Set.univ p ∈ M.parents.roots :=
      M.roots_eq.symm ▸ (C.boundaryEndAsVertex Set.univ p).property
    have q_root : C.boundaryEndVertex Set.univ q ∈ M.parents.roots :=
      M.roots_eq.symm ▸ (C.boundaryEndAsVertex Set.univ q).property
    have different : C.boundaryEndVertex Set.univ p ≠ C.boundaryEndVertex Set.univ q :=
      K.folding.boundaryEndVertex_ne_turn Set.univ p
    have crossing : C.SubtreeCrossingBank M.selection e bank ↔
        C.boundaryEndVertex Set.univ p = e ∨ C.boundaryEndVertex Set.univ q = e := by
      change ((M.parents.Ancestor (C.boundaryEndVertex Set.univ p) e ∧
          ¬ M.parents.Ancestor (C.boundaryEndVertex Set.univ q) e) ∨
        (M.parents.Ancestor (C.boundaryEndVertex Set.univ q) e ∧
          ¬ M.parents.Ancestor (C.boundaryEndVertex Set.univ p) e)) ↔ _
      rw [M.root_descendant_iff p_root, M.root_descendant_iff q_root]
      have separate : ¬ (C.boundaryEndVertex Set.univ p = e ∧
          C.boundaryEndVertex Set.univ q = e) :=
        fun both => different (both.1.trans both.2.symm)
      tauto
    rw [crossing]
    constructor
    · rintro (first | last)
      · exact ⟨p, first, Subtype.ext rfl⟩
      · refine ⟨q, last, ?_⟩
        simp only [q, TriangleComplex.boundaryTurn, Equiv.apply_symm_apply]
        exact Subtype.ext rfl
    · rintro ⟨r, vertex, named⟩
      have same_bank : (C.boundaryEndEquiv Set.univ r).1 = b :=
        Subtype.ext (congrArg Subtype.val named).symm
      have same : (C.boundaryEndEquiv Set.univ r).1 =
          (C.boundaryEndEquiv Set.univ p).1 := same_bank
      rcases (C.boundaryEnd_bank_eq_iff Set.univ r p).mp same with equal | equal
      · exact Or.inl ((congrArg (C.boundaryEndVertex Set.univ) equal).symm.trans vertex)
      · exact Or.inr ((congrArg (C.boundaryEndVertex Set.univ) equal).symm.trans vertex)
  · have selected := C.selectedCut_to_selection_link M.selection
      (C.relativeCutGraph_bank_link (Set.subset_univ _) s side)
    have no_crossing : ¬ C.SubtreeCrossingBank M.selection e
        (C.relativeCutBank M.retain Set.univ s side) := by
      obtain ⟨v, _, endpoints⟩ := selected
      have ne : v.val ≠ e := fun equal => v.property (equal ▸ root)
      have same := M.parents.ancestor_parent_iff ne
      let l := C.relativeBoundaryVertex (Set.subset_univ M.retain)
        ((C.boundaryGraph M.retain).left (C.relativeCutBank M.retain Set.univ s side))
      let r := C.relativeBoundaryVertex (Set.subset_univ M.retain)
        ((C.boundaryGraph M.retain).right (C.relativeCutBank M.retain Set.univ s side))
      change ¬ ((M.parents.Ancestor l e ∧ ¬ M.parents.Ancestor r e) ∨
        (M.parents.Ancestor r e ∧ ¬ M.parents.Ancestor l e))
      rcases endpoints with ⟨first, last⟩ | ⟨first, last⟩
      · change l = v.val at first
        change r = M.parents.parent v.val at last
        rw [first, last]
        tauto
      · change l = M.parents.parent v.val at first
        change r = v.val at last
        rw [first, last]
        tauto
    have no_old : ¬ ∃ p : C.BoundaryEnd Set.univ,
        C.boundaryEndVertex Set.univ p = e ∧
          C.relativeCutBank M.retain Set.univ s side =
            C.oldBoundaryBank (Set.subset_univ _) (C.boundaryEndEquiv Set.univ p).1 := by
      rintro ⟨p, _, named⟩
      exact C.relativeCutBank_not_old s side
        (congrArg Subtype.val named ▸ (C.boundaryEndEquiv Set.univ p).1.property)
    exact iff_of_false no_crossing no_old

/-- Exactly two original rim banks delimit every root's complete descendant region. -/
theorem exists_oriented_root_subtree_exits (e : C.Vertex Set.univ)
    (root : e ∈ M.parents.roots) :
    ∃ enter leave : Fin (M.projectionContour.length + 1), enter ≠ leave ∧
      (¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e enter ∧
        C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) enter)) ∧
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e leave ∧
        ¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave →
        (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) i) ↔
            C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e i) := by
  have boundary : C.IsBoundaryVertex Set.univ e := (Set.ext_iff.mp M.roots_eq e).mp root
  obtain ⟨germ, fixed⟩ := (C.isBoundaryVertex_iff_linkMate_fixed Set.univ e).mp boundary
  let p : C.BoundaryEnd Set.univ := ⟨germ.val,
    (C.mateGerm_eq_self_iff Set.univ germ.val).mp (congrArg Subtype.val fixed)⟩
  have vertex_p : C.boundaryEndVertex Set.univ p = e := germ.property
  obtain ⟨a, b, ne, two⟩ := C.boundaryEnd_two_at_vertex Set.univ p
  have vertex_a : C.boundaryEndVertex Set.univ a = e :=
    ((two a).mpr (Or.inl rfl)).trans vertex_p
  have vertex_b : C.boundaryEndVertex Set.univ b = e :=
    ((two b).mpr (Or.inr rfl)).trans vertex_p
  let banks := C.boundaryCycleBankEquiv M.retain M.projectionContour.cycle
    M.projectionContour.covers
  let index (q : C.BoundaryEnd Set.univ) := banks.symm
    (C.oldBoundaryBank (Set.subset_univ M.retain) (C.boundaryEndEquiv Set.univ q).1)
  have bank_at (q : C.BoundaryEnd Set.univ) :
      banks (index q) =
        C.oldBoundaryBank (Set.subset_univ _) (C.boundaryEndEquiv Set.univ q).1 :=
    banks.apply_symm_apply _
  have different : index a ≠ index b := by
    intro equal
    have named := (bank_at a).symm.trans ((congrArg banks equal).trans (bank_at b))
    have original : (C.boundaryEndEquiv Set.univ a).1 =
        (C.boundaryEndEquiv Set.univ b).1 :=
      Subtype.ext (congrArg (fun bank : C.BoundaryBank M.retain => bank.val) named)
    exact ne (K.folding.boundaryEnd_eq_of_same_bank_vertex Set.univ a b original
      (vertex_a.trans vertex_b.symm))
  apply exists_oriented_two_exits (finRotate (M.projectionContour.length + 1))
    (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e) (index a) (index b)
    different
  intro i
  have changes := C.subtree_boundary_change_iff M.selection M.projectionContour.cycle
    M.projectionContour.closes e i
  rw [← changes]
  change C.SubtreeCrossingBank M.selection e (banks i) ↔ i = index a ∨ i = index b
  rw [M.root_subtreeCrossingBank_iff e root]
  constructor
  · rintro ⟨q, vertex_q, named⟩
    have q_index : i = index q := banks.injective (named.trans (bank_at q).symm)
    have either := (two q).mp (vertex_q.trans vertex_p.symm)
    rcases either with rfl | rfl
    · exact Or.inl q_index
    · exact Or.inr q_index
  · rintro (rfl | rfl)
    · exact ⟨a, vertex_a, bank_at a⟩
    · exact ⟨b, vertex_b, bank_at b⟩

end Unfoldings.ConvexCap.SectorForest
