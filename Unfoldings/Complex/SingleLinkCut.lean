module

public import Unfoldings.Complex.RetainedCornerChain

/-! Opening one pair in an original cyclic link preserves its complete corner star and angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) {v : C.Vertex Set.univ}

/-- All interior chain pairings survive when only its two outer paired germs are opened. -/
theorem exists_spanning_chain_of_single_link_cut (internal : ¬ C.IsBoundaryVertex Set.univ v)
    (p : C.LinkGerm Set.univ v)
    (preserves : ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val) :
    ∃ n, ∃ c : (C.linkSystem Set.univ v).Chain n, c.first = p ∧ (∀ q, c.Visited q) ∧
      ∀ k : Fin n, C.GermCrosses retain (C.turnGerm (c.point k.castSucc).val)
        (c.point k.succ).val := by
  have free (q : C.LinkGerm Set.univ v) : C.linkMate Set.univ v q ≠ q := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ v).mpr ⟨q, fixed⟩)
  obtain ⟨n, c, first, closes, covers⟩ := (C.linkSystem Set.univ v).exists_cycle_chain
    (C.linkSystem_connected Set.univ v) free p
  refine ⟨n, c, first, covers, fun k => ?_⟩
  have start : C.linkMate Set.univ v c.first = C.linkTurn Set.univ v c.last := by
    calc
      _ = C.linkMate Set.univ v
          (C.linkMate Set.univ v (C.linkTurn Set.univ v c.last)) := congrArg _ closes.symm
      _ = _ := C.linkMate_involutive Set.univ v _
  have first_ne : C.linkTurn Set.univ v (c.point k.castSucc) ≠ p := by
    rw [← first]
    intro equal
    exact c.disjoint 0 k.castSucc equal.symm
  have last_ne : C.linkTurn Set.univ v (c.point k.castSucc) ≠ C.linkMate Set.univ v p := by
    rw [← first, start]
    intro equal
    have same := (C.linkTurn_involutive Set.univ v).injective equal
    change c.point k.castSucc = c.point (Fin.last n) at same
    have values := congrArg Fin.val (c.injective same)
    simp only [Fin.val_castSucc, Fin.val_last] at values
    omega
  exact preserves _ _ first_ne last_ne (C.chain_next_crosses Set.univ v c k)

/-- The opened cyclic star has one actual cut vertex copy. -/
theorem unique_vertex_copy_of_single_link_cut (internal : ¬ C.IsBoundaryVertex Set.univ v)
    (p : C.LinkGerm Set.univ v)
    (preserves : ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val)
    (w : C.Vertex retain) (original : C.vertexForgetCuts (Set.subset_univ retain) w = v) :
    w = C.vertexOfCorner retain p.val.1 := by
  obtain ⟨n, c, first, covers, crossings⟩ :=
    C.exists_spanning_chain_of_single_link_cut retain internal p preserves
  have same := C.unique_vertex_copy_of_retained_chain retain c crossings covers w original
  rwa [first] at same

/-- The retained star has the original intrinsic angle, with no deficit input. -/
theorem totalAngle_of_single_link_cut (internal : ¬ C.IsBoundaryVertex Set.univ v)
    (p : C.LinkGerm Set.univ v)
    (preserves : ∀ q r : C.LinkGerm Set.univ v, q ≠ p → q ≠ C.linkMate Set.univ v p →
      C.GermCrosses Set.univ q.val r.val → C.GermCrosses retain q.val r.val) :
    C.totalAngle retain (C.vertexOfCorner retain p.val.1) = C.totalAngle Set.univ v := by
  obtain ⟨n, c, first, covers, crossings⟩ :=
    C.exists_spanning_chain_of_single_link_cut retain internal p preserves
  have angle := C.totalAngle_of_retained_chain retain c crossings covers
  rwa [first] at angle

end Unfoldings.TriangleComplex
