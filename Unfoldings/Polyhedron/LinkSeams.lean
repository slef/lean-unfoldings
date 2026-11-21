module

public import Unfoldings.Polyhedron.LabeledComponentCount
public import Unfoldings.Polyhedron.LinkDirections
public import Unfoldings.Combinatorics.LabelChanges
public import Unfoldings.Topology.CyclicLabels

/-! A cyclic link indexes each incident original seam exactly once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

/-- The unique original seam supporting an edge germ. -/
def germSeam (p : C.Germ) : C.Seam :=
  (P.seamSideEquiv.symm ((C.germEdge p).face, (C.germEdge p).edge)).1

theorem germSeam_germOfEndpoint (s : C.Seam) (b k : Bool) :
    P.germSeam (C.germOfEndpoint (C.seamSide s b) k) = s := by
  unfold germSeam
  rw [C.germEdge_germOfEndpoint]
  change (P.seamSideEquiv.symm (P.seamSideEquiv (s, b))).1 = s
  rw [P.seamSideEquiv.symm_apply_apply]

theorem exists_germSeam_side (p : C.Germ) :
    ∃ b : Bool, p = C.germOfEndpoint (C.seamSide (P.germSeam p) b) p.2 := by
  let a := P.seamSideEquiv.symm ((C.germEdge p).face, (C.germEdge p).edge)
  have e := P.seamSideEquiv.apply_symm_apply ((C.germEdge p).face, (C.germEdge p).edge)
  change ((C.seamSide a.1 a.2).face, (C.seamSide a.1 a.2).edge) = _ at e
  have side : C.seamSide (P.germSeam p) a.2 = C.germEdge p :=
    congrArg (fun t : Face × Fin 3 => EdgeRef.mk t.1 t.2) e
  exact ⟨a.2, by rw [side, C.germOfEndpoint_germEdge]⟩

theorem germSeam_mate (p : C.Germ) :
    P.germSeam (C.mateGerm Set.univ p) = P.germSeam p := by
  let s := P.germSeam p
  obtain ⟨b, h⟩ := P.exists_germSeam_side p
  let other := C.germOfEndpoint (C.seamSide s (!b)) (C.acrossEndpoint s b p.2)
  have cross : C.GermCrosses Set.univ p other :=
    ⟨s, Set.mem_univ _, b, p.2, h, rfl⟩
  rw [C.mateGerm_of_crossing cross]
  exact P.germSeam_germOfEndpoint s _ _

private theorem exists_left_germ {p : C.Germ} :
    ∃ b : Bool,
      (p = C.germOfEndpoint (C.left (P.germSeam p)) b ∨
        C.mateGerm Set.univ p = C.germOfEndpoint (C.left (P.germSeam p)) b) := by
  let s := P.germSeam p
  obtain ⟨b, h⟩ := P.exists_germSeam_side p
  cases b
  · exact ⟨p.2, Or.inl h⟩
  · let k := C.acrossEndpoint s true p.2
    have cross : C.GermCrosses Set.univ p (C.germOfEndpoint (C.left s) k) :=
      ⟨s, Set.mem_univ _, true, p.2, h, rfl⟩
    exact ⟨k, Or.inr (C.mateGerm_of_crossing cross)⟩

theorem germSeam_mem_incidentSeams {a : C.Vertex Set.univ} (p : C.LinkGerm Set.univ a) :
    P.germSeam p.val ∈ incidentSeams a := by
  classical
  obtain ⟨b, h | h⟩ := P.exists_left_germ (p := p.val)
  all_goals
    have eq : a = C.seamVertex (P.germSeam p.val) b := by
      first
      | exact p.property.symm.trans (congrArg (fun z : C.Germ =>
          C.vertexOfCorner Set.univ z.1) h)
      | exact p.property.symm.trans ((C.mateGerm_vertex_eq Set.univ p.val).symm.trans
          (congrArg (fun z : C.Germ => C.vertexOfCorner Set.univ z.1) h))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases b
    · exact Or.inl eq
    · exact Or.inr eq

include P in
theorem eq_or_mate_of_germSeam_eq {a : C.Vertex Set.univ} (p q : C.LinkGerm Set.univ a)
    (same : P.germSeam p.val = P.germSeam q.val) :
    p = q ∨ C.linkMate Set.univ a p = q := by
  obtain ⟨b, hp⟩ := P.exists_left_germ (p := p.val)
  obtain ⟨d, hq⟩ := P.exists_left_germ (p := q.val)
  rw [← same] at hq
  let s := P.germSeam p.val
  have endpoint_of_germ (x : C.LinkGerm Set.univ a) (k : Bool)
      (h : x.val = C.germOfEndpoint (C.left s) k ∨
        C.mateGerm Set.univ x.val = C.germOfEndpoint (C.left s) k) :
      C.seamVertex s k = a := by
    rcases h with h | h
    · exact (congrArg (fun z : C.Germ => C.vertexOfCorner Set.univ z.1) h).symm.trans x.property
    · exact (congrArg (fun z : C.Germ => C.vertexOfCorner Set.univ z.1) h).symm.trans
        ((C.mateGerm_vertex_eq Set.univ x.val).trans x.property)
  have endpoints := (endpoint_of_germ p b hp).trans (endpoint_of_germ q d hq).symm
  have same_end : b = d := by
    have distinct : C.seamVertex s false ≠ C.seamVertex s true := fun h =>
      gaussianSiteOfVertex_seam_ne (F := F) s
        (congrArg (fun z => (F.gaussianSiteOfVertex z : Space)) h)
    cases b <;> cases d
    · rfl
    · exact (distinct endpoints).elim
    · exact (distinct endpoints.symm).elim
    · rfl
  subst d
  rcases hp with h | h <;> rcases hq with k | k
  · exact Or.inl (Subtype.ext (h.trans k.symm))
  · right
    apply Subtype.ext
    have opposite := congrArg (C.mateGerm Set.univ) (h.trans k.symm)
    rwa [C.mateGerm_involutive] at opposite
  · exact Or.inr (Subtype.ext (h.trans k.symm))
  · exact Or.inl (Subtype.ext ((C.mateGerm_involutive Set.univ).injective (h.trans k.symm)))

open Classical in
/-- A cyclic chain's initial germs represent all seams at the vertex. -/
def linkSeamEquiv {a : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ a).Chain n)
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p) : Fin (n + 1) ≃ ↑(incidentSeams a) := by
  let side (i : Fin (n + 1)) : ↑(incidentSeams a) :=
    ⟨P.germSeam (c.point i).val, P.germSeam_mem_incidentSeams (c.point i)⟩
  refine Equiv.ofBijective side ⟨?_, ?_⟩
  · intro i j h
    rcases P.eq_or_mate_of_germSeam_eq (c.point i) (c.point j) (congrArg Subtype.val h) with eq | eq
    · exact c.injective eq
    · exact (c.mate_point_ne_point closes i j eq).elim
  · intro s
    have endpoint : ∃ b : Bool, C.seamVertex s.val b = a := by
      rcases (Finset.mem_filter.mp s.property).2 with v | v
      · exact ⟨false, v.symm⟩
      · exact ⟨true, v.symm⟩
    obtain ⟨b, hb⟩ := endpoint
    let p : C.LinkGerm Set.univ a := ⟨C.germOfEndpoint (C.left s.val) b, hb⟩
    have seam : P.germSeam p.val = s.val := P.germSeam_germOfEndpoint s.val false b
    obtain ⟨i, h | h⟩ := covers p
    · refine ⟨i, Subtype.ext ?_⟩
      exact (congrArg (P.germSeam ∘ Subtype.val) h).symm.trans seam
    · have next : ∃ j, C.linkMate Set.univ a p = c.point j := by
        rw [h]
        refine Fin.lastCases ?_ (fun k => ?_) i
        · exact ⟨0, closes⟩
        · exact ⟨k.succ, c.next k⟩
      obtain ⟨j, j_eq⟩ := next
      refine ⟨j, Subtype.ext ?_⟩
      exact (congrArg (P.germSeam ∘ Subtype.val) j_eq).symm.trans
        ((P.germSeam_mate p.val).trans seam)

/-- A label change across a germ is the same change across its named seam. -/
theorem labelChange_germSeam_iff {L : Type*} (label : Face → L) (p : C.Germ) :
    label p.1.1 ≠ label (C.mateGerm Set.univ p).1.1 ↔
      label (C.left (P.germSeam p)).face ≠ label (C.right (P.germSeam p)).face := by
  let s := P.germSeam p
  obtain ⟨b, h⟩ := P.exists_germSeam_side p
  let other := C.germOfEndpoint (C.seamSide s (!b)) (C.acrossEndpoint s b p.2)
  have cross : C.GermCrosses Set.univ p other :=
    ⟨s, Set.mem_univ _, b, p.2, h, rfl⟩
  have face := congrArg (fun q : C.Germ => q.1.1) h
  change p.1.1 = (C.seamSide s b).face at face
  rw [face, C.mateGerm_of_crossing cross]
  change label (C.seamSide s b).face ≠ label (C.seamSide s (!b)).face ↔
    label (C.left s).face ≠ label (C.right s).face
  cases b
  · rfl
  · exact ne_comm

open Classical in
include P in
/-- Counting changes in the cyclic link gives the cut degree in the original mesh. -/
theorem labelCutDegree_eq_linkChanges {L : Type*} (label : Face → L)
    {a : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ a).Chain n)
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    labelCutDegree label a =
      (Finset.univ.filter fun i : Fin (n + 1) =>
        label (c.point i).val.1.1 ≠ label (C.linkMate Set.univ a (c.point i)).val.1.1).card := by
  let e := P.linkSeamEquiv c closes covers
  let cut (s : C.Seam) := label (C.left s).face ≠ label (C.right s).face
  let changed (i : Fin (n + 1)) :=
    label (c.point i).val.1.1 ≠ label (C.linkMate Set.univ a (c.point i)).val.1.1
  have change_on_side (i : Fin (n + 1)) : changed i ↔ cut (e i).val :=
    P.labelChange_germSeam_iff label (c.point i).val
  change ((incidentSeams a).filter cut).card = (Finset.univ.filter changed).card
  symm
  refine Finset.card_bij (fun i _ => (e i).val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property, (change_on_side i).mp (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ equal
    exact e.injective (Subtype.ext equal)
  · intro s hs
    obtain ⟨base, different⟩ := Finset.mem_filter.mp hs
    let j := e.symm ⟨s, base⟩
    have same : e j = ⟨s, base⟩ := e.apply_symm_apply _
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (change_on_side j).mpr ?_⟩,
      congrArg Subtype.val same⟩
    rwa [same]

/-- The mate of an incoming germ has the face of the preceding link corner. -/
theorem linkFace_mate_eq_prev {a : C.Vertex Set.univ} {n : ℕ}
    (c : (C.linkSystem Set.univ a).Chain n)
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (i : Fin (n + 1)) :
    (C.linkMate Set.univ a (c.point i)).val.1.1 =
      (c.point ((finRotate (n + 1)).symm i)).val.1.1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have start : C.linkMate Set.univ a c.first = C.linkTurn Set.univ a c.last := by
      rw [← closes, C.linkMate_involutive]
    rw [finRotate_symm_zero]
    have eq := congrArg (fun p : C.LinkGerm Set.univ a => p.val.1.1) start
    exact eq
  · rw [finRotate_symm_succ]
    have eq := congrArg (fun p : C.LinkGerm Set.univ a => p.val.1.1) (c.mate_succ k)
    exact eq

include P in
/-- A face labeling cannot change exactly once around an original vertex. -/
theorem labelCutDegree_ne_one {L : Type*} (label : Face → L) (a : C.Vertex Set.univ) :
    labelCutDegree label a ≠ 1 := by
  classical
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link a
  rw [P.labelCutDegree_eq_linkChanges label c closes covers]
  simp only [linkFace_mate_eq_prev c closes]
  exact card_label_changes_ne_one (finRotate (n + 1)).symm (fun i => label (c.point i).val.1.1)

end Unfoldings.SpatialFolding.ConvexBoundary
