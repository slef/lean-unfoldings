module

public import Unfoldings.Polyhedron.GaussianCornerAngle
public import Unfoldings.Polyhedron.GaussianNondegenerate
public import Unfoldings.Polyhedron.GaussianArcValence

/-! The compressed normal cycle at an extreme vertex is a simple cycle of
genuine original dual arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

/-- The actual normal directions indexed by the starts of constant runs. -/
def compressedLinkNormal : Fin (m + 1) → Space :=
  linkNormals N c ∘ cyclicRunStart (linkNormals N c) count

theorem compressedLinkNormal_ne_next (k : Fin (m + 1)) :
    compressedLinkNormal N c count k ≠ compressedLinkNormal N c count (finRotate (m + 1) k) := by
  let start := cyclicRunStart (linkNormals N c) count
  have change := (mem_cyclicRunStarts _ _).mp (cyclicRunStart_mem (linkNormals N c) count
    (finRotate (m + 1) k))
  have previous := label_predecessor_cyclicRunStart (linkNormals N c) count k
  intro eq
  exact change (previous.trans eq)

/-- The seam at a run start joins the preceding compressed normal and the
normal of the new run. -/
theorem compressedLinkNormal_arcEnds (k : Fin (m + 1)) :
    let p := compressedLinkNormal N c count
    let s := (P.runStartGaussianSeamEquiv N c closes covers count k).val
    HasGaussianArcEnds N s (p ((finRotate (m + 1)).symm k)) (p k) := by
  let prev := (finRotate (m + 1)).symm k
  let at_k := cyclicRunStart (linkNormals N c) count k
  let g := (c.point at_k).val
  have run := label_predecessor_cyclicRunStart (linkNormals N c) count prev
  change linkNormals N c ((finRotate (n + 1)).symm
      (cyclicRunStart (linkNormals N c) count
        ((finRotate (m + 1)) ((finRotate (m + 1)).symm k)))) =
    compressedLinkNormal N c count prev at run
  rw [Equiv.apply_symm_apply] at run
  change N.normal (c.point ((finRotate (n + 1)).symm at_k)).val.1.1 =
    compressedLinkNormal N c count prev at run
  rw [← linkFace_mate_eq_prev c closes at_k] at run
  have run' : N.normal (C.mateGerm Set.univ g).1.1 = compressedLinkNormal N c count prev := run
  change HasGaussianArcEnds N (P.germSeam g) (compressedLinkNormal N c count prev)
    (N.normal g.1.1)
  unfold HasGaussianArcEnds
  rcases P.germSeam_faces g with ⟨left, right⟩ | ⟨left, right⟩
  · exact Or.inr ⟨congrArg N.normal left.symm, (congrArg N.normal right.symm).trans run'⟩
  · exact Or.inl ⟨(congrArg N.normal left.symm).trans run', congrArg N.normal right.symm⟩

theorem HasGaussianArcEnds.symm {s : C.Seam} {x y : Space}
    (h : HasGaussianArcEnds N s x y) : HasGaussianArcEnds N s y x := Or.symm h

include P closes covers in
/-- An extreme Gaussian cell cannot repeat a normal vertex in a
nonconsecutive position of its compressed link. -/
theorem compressedLinkNormal_injective
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ) :
    Function.Injective (compressedLinkNormal N c count) := by
  let p := compressedLinkNormal N c count
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  let next := finRotate (m + 1)
  let start := cyclicRunStart (linkNormals N c) count
  intro i j equal
  change p i = p j at equal
  by_contra different
  have not_next : next i ≠ j := fun h =>
    compressedLinkNormal_ne_next N c count i (equal.trans (congrArg p h).symm)
  have step : next i ≠ i := fun h =>
    compressedLinkNormal_ne_next N c count i (congrArg p h.symm)
  let k : Fin 3 → Fin (m + 1) := ![i, next i, j]
  have distinct : Function.Injective k := by
    intro u v h
    fin_cases u <;> fin_cases v
    all_goals first
      | rfl
      | exact (different h).elim
      | exact (different h.symm).elim
      | exact (not_next h).elim
      | exact (not_next h.symm).elim
      | exact (step h).elim
      | exact (step h.symm).elim
  let y : Fin 3 → Space := ![p (next.symm i), p (next i), p (next.symm j)]
  have end_i := P.compressedLinkNormal_arcEnds N c closes covers count i
  have end_j := P.compressedLinkNormal_arcEnds N c closes covers count j
  have end_n := P.compressedLinkNormal_arcEnds N c closes covers count (next i)
  change HasGaussianArcEnds N (s (next i)).val (p (next.symm (next i))) (p (next i)) at end_n
  rw [next.symm_apply_apply] at end_n
  have ends : ∀ l : Fin 3, HasGaussianArcEnds N (s (k l)).val (p i) (y l) := by
    intro l
    fin_cases l
    · exact end_i.symm
    · exact end_n
    · change HasGaussianArcEnds N (s j).val (p i) (p (next.symm j))
      rw [equal]
      exact end_j.symm
  have prev_ne (b : Fin (m + 1)) : p b ≠ p (next.symm b) := by
    have h := compressedLinkNormal_ne_next N c count (next.symm b)
    change p (next.symm b) ≠ p (next (next.symm b)) at h
    rw [next.apply_symm_apply] at h
    exact Ne.symm h
  have genuine : ∀ l : Fin 3, p i ≠ y l := by
    intro l
    fin_cases l
    · exact prev_ne i
    · exact compressedLinkNormal_ne_next N c count i
    · change p i ≠ p (next.symm j)
      rw [equal]
      exact prev_ne j
  have incident : ∀ l : Fin 3, ∃ (f : Face) (u : Fin 3),
      C.vertexOfCorner Set.univ (f, u) = a ∧ N.normal f = y l := by
    intro l
    have member : y l ∈ Set.range p := by
      fin_cases l
      · exact ⟨next.symm i, rfl⟩
      · exact ⟨next i, rfl⟩
      · exact ⟨next.symm j, rfl⟩
    change y l ∈ Set.range (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) at member
    rwa [range_compressed_linkNormals N c covers count] at member
  have adjacent (l : Fin 3) :
      ∃ b : C.Vertex Set.univ, C.seamGraph.IsLink (s (k l)).val a b := by
    obtain ⟨b, link, _⟩ := P.exists_linked_vertex_of_germDirection (c.point (start (k l)))
    exact ⟨b, link⟩
  choose other links using adjacent
  exact P.false_of_three_gaussian_arcs_sharing_endpoint N extreme (fun l => (s (k l)).val)
    (Subtype.val_injective.comp (s.injective.comp distinct)) other links (p i) y
    genuine ends incident

include P N closes covers count in
/-- The simple compressed boundary of an extreme Gaussian cell has at least three sides. -/
theorem three_le_count_compressedLinkNormal
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ) :
    3 ≤ m + 1 := by
  by_contra small
  have nonzero : m ≠ 0 := by
    rintro rfl
    have equal : finRotate 1 0 = 0 := Subsingleton.elim _ _
    exact compressedLinkNormal_ne_next N c count 0
      (congrArg (compressedLinkNormal N c count) equal.symm)
  have two : m = 1 := by omega
  subst m
  let p := compressedLinkNormal N c count
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  let start := cyclicRunStart (linkNormals N c) count
  obtain ⟨b, h, _⟩ := P.exists_linked_vertex_of_germDirection (c.point (start 0))
  obtain ⟨d, j, _⟩ := P.exists_linked_vertex_of_germDirection (c.point (start 1))
  have first := P.compressedLinkNormal_arcEnds N c closes covers count 0
  have second := P.compressedLinkNormal_arcEnds N c closes covers count 1
  change HasGaussianArcEnds N (s 0).val (p ((finRotate 2).symm 0)) (p 0) at first
  change HasGaussianArcEnds N (s 1).val (p ((finRotate 2).symm 1)) (p 1) at second
  rw [show (finRotate 2).symm 0 = 1 from finRotate_symm_zero 1] at first
  rw [show (finRotate 2).symm 1 = 0 from finRotate_symm_succ (0 : Fin 1)] at second
  have xy : p 0 ≠ p 1 := compressedLinkNormal_ne_next N c count 0
  have different : (s 0).val ≠ (s 1).val := fun eq =>
    (by decide : (0 : Fin 2) ≠ 1) (s.injective (Subtype.ext eq))
  exact P.false_of_distinct_seams_with_same_arcEnds N extreme different h j xy first.symm second

end Unfoldings.SpatialFolding.ConvexBoundary
