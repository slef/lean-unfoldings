module

public import Unfoldings.Complex.ContourFirstVisit
public import Unfoldings.Complex.IncidentSeamFans
public import Unfoldings.Topology.ChildSubtrees

/-! The cut status outside a child block stays fixed while that subtree is traversed. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)

local notation "Block" => C.contourParentInterval S Q roots starts child nonroot

include roots starts nonroot in
/-- Two positions inside one child block have the same processed vertices outside its
proper descendants, after each named position has been processed. -/
theorem contourFrontier_processed_iff_of_child_block
    (a b : Fin Q.length)
    (inside_a : P.Ancestor (C.contourOriginalVertex S Q a.castSucc) child)
    (inside_b : P.Ancestor (C.contourOriginalVertex S Q b.castSucc) child)
    (vertex : C.Vertex Set.univ)
    (outside : ¬ P.Ancestor vertex child ∨ vertex = child) :
    vertex ∈ (C.contourFrontier S Q a.succ).processed ↔
      vertex ∈ (C.contourFrontier S Q b.succ).processed := by
  by_cases at_root : vertex ∈ P.roots
  · exact iff_of_true ((C.contourFrontier S Q a.succ).roots at_root)
      ((C.contourFrontier S Q b.succ).roots at_root)
  let apart := C.contourParentInterval S Q roots starts vertex at_root
  let entry := finRotate (Q.length + 1) apart.enter
  have first : C.contourOriginalVertex S Q entry = vertex :=
    C.contourOriginalVertex_after_enter S Q roots starts vertex at_root
  have rank : entry.val = apart.enter.val + 1 :=
    C.contourParentInterval_enter_succ_val S Q roots starts vertex at_root
  have in_a : (Block).enter.val < a.val ∧ a.val ≤ (Block).leave.val :=
    ((Block).subtree a.castSucc).mp inside_a
  have in_b : (Block).enter.val < b.val ∧ b.val ≤ (Block).leave.val :=
    ((Block).subtree b.castSucc).mp inside_b
  have at_a : vertex ∈ (C.contourFrontier S Q a.succ).processed ↔ entry.val ≤ a.val := by
    rw [C.mem_contourFrontier_processed_iff_enter S Q roots starts vertex at_root, rank]
    exact Nat.lt_succ_iff
  have at_b : vertex ∈ (C.contourFrontier S Q b.succ).processed ↔ entry.val ≤ b.val := by
    rw [C.mem_contourFrontier_processed_iff_enter S Q roots starts vertex at_root, rank]
    exact Nat.lt_succ_iff
  rw [at_a, at_b]
  rcases outside with other | same
  · have unchanged (x y : Fin Q.length) (inside_x : (Block).enter.val < x.val)
        (inside_y : y.val ≤ (Block).leave.val) (earlier : entry.val ≤ y.val) :
        entry.val ≤ x.val := by
      by_contra! between
      have at_entry : P.Ancestor (C.contourOriginalVertex S Q entry) child :=
        ((Block).subtree entry).mpr ⟨inside_x.trans between, earlier.trans inside_y⟩
      exact other (first ▸ at_entry)
    exact ⟨unchanged b a in_b.1 in_a.2, unchanged a b in_a.1 in_b.2⟩
  · have enter_congr (u v : C.Vertex Set.univ) (hu : u ∉ P.roots) (hv : v ∉ P.roots)
        (equal : u = v) :
        (C.contourParentInterval S Q roots starts u hu).enter =
          (C.contourParentInterval S Q roots starts v hv).enter := by
      subst v
      rfl
    have first_rank : entry.val = (Block).enter.val + 1 := rank.trans
      (congrArg (fun i : Fin (Q.length + 1) => i.val + 1)
        (enter_congr vertex child at_root nonroot same))
    exact iff_of_true (first_rank.trans_le (Nat.succ_le_of_lt in_a.1))
      (first_rank.trans_le (Nat.succ_le_of_lt in_b.1))

include roots starts nonroot in
/-- Throughout a child's block the two-dimensional corner gates at its parent
have the same original cut status. This includes the incoming child and every sibling. -/
theorem mem_processedParentRetain_iff_of_child_block
    (a b : Fin Q.length)
    (inside_a : P.Ancestor (C.contourOriginalVertex S Q a.castSucc) child)
    (inside_b : P.Ancestor (C.contourOriginalVertex S Q b.castSucc) child)
    (s : C.Seam) (incident : ∃ other, C.seamGraph.IsLink s (P.parent child) other) :
    s ∈ C.processedParentRetain S (C.contourFrontier S Q a.succ) ↔
      s ∈ C.processedParentRetain S (C.contourFrontier S Q b.succ) := by
  classical
  obtain ⟨other, at_parent⟩ := incident
  have selector (v : {v : C.Vertex Set.univ // v ∉ P.roots}) (named : S.edge v = s) :
      ¬ P.Ancestor v.val child ∨ v.val = child := by
    have link : C.seamGraph.IsLink s v.val (P.parent v.val) := named ▸ S.link v
    rcases at_parent.eq_and_eq_or_eq_and_eq link with same | sibling
    · exact Or.inl (same.1 ▸ P.not_ancestor_parent_self nonroot)
    · by_cases equal : v.val = child
      · exact Or.inr equal
      · refine Or.inl (fun source => equal ?_)
        exact P.child_ancestor_unique v.property nonroot sibling.1.symm rfl
          (P.ancestor_refl v.val) source
  apply not_iff_not.mp
  rw [C.not_mem_processedParentRetain_iff, C.not_mem_processedParentRetain_iff]
  constructor
  · rintro ⟨v, reached, same⟩
    exact ⟨v, (C.contourFrontier_processed_iff_of_child_block S Q roots starts child nonroot
      a b inside_a inside_b v.val (selector v same)).mp reached, same⟩
  · rintro ⟨v, reached, same⟩
    exact ⟨v, (C.contourFrontier_processed_iff_of_child_block S Q roots starts child nonroot
      a b inside_a inside_b v.val (selector v same)).mpr reached, same⟩

local notation "RetainAfter[" i "]" =>
  C.processedParentRetain S (C.contourFrontier S Q (Fin.succ i))

include roots starts in
private theorem retainAfter_subset_of_le (a b : Fin Q.length) (ordered : a ≤ b) :
    RetainAfter[b] ⊆ RetainAfter[a] := by
  apply C.processedParentRetain_antitone S
  intro v hv
  rw [C.rim_contour_processed_iff_of_boundary_roots S roots Q starts] at hv ⊢
  rcases hv with root | ⟨i, before, y⟩
  · exact Or.inl root
  · exact Or.inr ⟨i, before.trans_le (Nat.succ_le_succ ordered), y⟩

include roots starts nonroot in
/-- An actual rootward bank at the parent sees exactly the same intrinsic fan angle
throughout the traversal of any one of its child subtrees. -/
theorem contour_child_block_totalAngle_eq
    (a b : Fin Q.length)
    (inside_a : P.Ancestor (C.contourOriginalVertex S Q a.castSucc) child)
    (inside_b : P.Ancestor (C.contourOriginalVertex S Q b.castSucc) child)
    (p : C.BoundaryEnd RetainAfter[a]) (q : C.BoundaryEnd RetainAfter[b])
    (anchor : p.val = q.val) (original : C.vertexOfCorner Set.univ p.val.1 = P.parent child) :
    C.totalAngle RetainAfter[a] (C.boundaryEndVertex RetainAfter[a] p) =
      C.totalAngle RetainAfter[b] (C.boundaryEndVertex RetainAfter[b] q) := by
  have agrees := C.mem_processedParentRetain_iff_of_child_block S Q roots starts child nonroot
    a b inside_a inside_b
  rcases le_total a b with earlier | later
  · have other : C.vertexOfCorner Set.univ q.val.1 = P.parent child := anchor ▸ original
    have included := C.retainAfter_subset_of_le S Q roots starts a b earlier
    exact (C.totalAngle_eq_of_incidentSeams included (P.parent child)
      (fun s h => (agrees s h).symm) q p anchor.symm other).symm
  · exact C.totalAngle_eq_of_incidentSeams (C.retainAfter_subset_of_le S Q roots starts b a later)
      (P.parent child) agrees p q anchor original

end Unfoldings.TriangleComplex
