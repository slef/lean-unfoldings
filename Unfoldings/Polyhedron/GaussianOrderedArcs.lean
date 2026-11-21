module

public import Unfoldings.Polyhedron.LinkSeams
public import Unfoldings.Combinatorics.CyclicRunCompression
public import Unfoldings.Geometry.MinorArcArclength

/-! The genuine normal arcs are traversed by compressing the original cyclic link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)

open Classical in
/-- The genuine dual arcs at an original vertex are the seams across distinct normals. -/
def gaussianArcSeams (N : F.SupportingNormals) (a : C.Vertex Set.univ) : Finset C.Seam :=
  (incidentSeams a).filter fun s => N.normal (C.left s).face ≠ N.normal (C.right s).face

/-- Normal labels of the original link's corners. -/
def linkNormals (c : (C.linkSystem Set.univ a).Chain n) : Fin (n + 1) → Space :=
  fun i => N.normal (c.point i).val.1.1

theorem germSeam_faces (p : C.Germ) :
    let s := P.germSeam p
    let f := p.1.1
    let g := (C.mateGerm Set.univ p).1.1
    (f = (C.left s).face ∧ g = (C.right s).face) ∨
      (g = (C.left s).face ∧ f = (C.right s).face) := by
  let s := P.germSeam p
  obtain ⟨b, h⟩ := P.exists_germSeam_side p
  let other := C.germOfEndpoint (C.seamSide s (!b)) (C.acrossEndpoint s b p.2)
  have cross : C.GermCrosses Set.univ p other :=
    ⟨s, Set.mem_univ _, b, p.2, h, rfl⟩
  have left := congrArg (fun q : C.Germ => q.1.1) h
  have right := congrArg (fun q : C.Germ => q.1.1) (C.mateGerm_of_crossing cross)
  change p.1.1 = (C.seamSide s b).face at left
  change (C.mateGerm Set.univ p).1.1 = (C.seamSide s (!b)).face at right
  cases b
  · exact Or.inl ⟨left, right⟩
  · exact Or.inr ⟨right, left⟩

theorem runStart_iff_genuine_seam
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (i : Fin (n + 1)) :
    i ∈ cyclicRunStarts (linkNormals N c) ↔
      P.germSeam (c.point i).val ∈ gaussianArcSeams N a := by
  classical
  rw [mem_cyclicRunStarts, gaussianArcSeams, Finset.mem_filter]
  have incident := P.germSeam_mem_incidentSeams (c.point i)
  have changes := P.labelChange_germSeam_iff N.normal (c.point i).val
  change (N.normal (c.point i).val.1.1 ≠
    N.normal (C.linkMate Set.univ a (c.point i)).val.1.1) ↔ _ at changes
  rw [linkFace_mate_eq_prev c closes i] at changes
  rw [and_iff_right incident, ← changes]
  exact ne_comm

open Classical in
/-- The increasing run-start order lists exactly the genuine seams, including
each original crease only once. -/
def runStartGaussianSeamEquiv
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p)
    {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1) :
    Fin (m + 1) ≃ ↑(gaussianArcSeams N a) := by
  let side i := P.linkSeamEquiv c closes covers i
  let start := cyclicRunStart (linkNormals N c) count
  let genuine (i : Fin (m + 1)) : ↑(gaussianArcSeams N a) := ⟨(side (start i)).val,
    (P.runStart_iff_genuine_seam N c closes _).mp (cyclicRunStart_mem _ _ i)⟩
  refine Equiv.ofBijective genuine ⟨?_, ?_⟩
  · intro i j h
    refine start.injective ((P.linkSeamEquiv c closes covers).injective (Subtype.ext ?_))
    have eq := congrArg (fun t : ↑(gaussianArcSeams N a) => t.val) h
    exact eq
  · intro s
    let base : ↑(incidentSeams a) := ⟨s.val, (Finset.mem_filter.mp s.property).1⟩
    let i := (P.linkSeamEquiv c closes covers).symm base
    have eq : side i = base := (P.linkSeamEquiv c closes covers).apply_symm_apply _
    have on_side : P.germSeam (c.point i).val = s.val := congrArg Subtype.val eq
    have member := (P.runStart_iff_genuine_seam N c closes i).mpr (on_side.symm ▸ s.property)
    obtain ⟨k, k_eq⟩ := exists_cyclicRunStart_of_mem (linkNormals N c) count member
    refine ⟨k, Subtype.ext ?_⟩
    change (side (start k)).val = s.val
    rw [show start k = i from k_eq]
    exact congrArg Subtype.val eq

/-- Each compressed normal is followed by the arc at the next run start.
The two endpoints agree with the actual incident face normals of that seam. -/
theorem runStart_closedMinorArc
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p)
    {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1) (i : Fin (m + 1)) :
    let next := finRotate (m + 1) i
    let normal (j : Fin (m + 1)) :=
      linkNormals N c (cyclicRunStart (linkNormals N c) count j)
    let s := (P.runStartGaussianSeamEquiv N c closes covers count next).val
    closedMinorArc (normal i) (normal next) =
      closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  let next := finRotate (m + 1) i
  let k := cyclicRunStart (linkNormals N c) count next
  let p := (c.point k).val
  let s := P.germSeam p
  have previous := label_predecessor_cyclicRunStart (linkNormals N c) count i
  change linkNormals N c ((finRotate (n + 1)).symm k) = _ at previous
  change closedMinorArc (linkNormals N c (cyclicRunStart (linkNormals N c) count i))
    (linkNormals N c k) = closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face)
  rw [← previous]
  change closedMinorArc (N.normal (c.point ((finRotate (n + 1)).symm k)).val.1.1)
    (N.normal p.1.1) = _
  rw [← linkFace_mate_eq_prev c closes k]
  change closedMinorArc (N.normal (C.mateGerm Set.univ p).1.1) (N.normal p.1.1) = _
  rcases P.germSeam_faces p with ⟨h, j⟩ | ⟨j, h⟩
  · rw [h, j, closedMinorArc_comm]
  · rw [h, j]

/-- The compressed normal cycle contains all incident outward normal directions. -/
theorem range_compressed_linkNormals
    (covers : ∀ p, c.Visited p)
    {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1) :
    Set.range (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) =
      {x | ∃ (f : Face) (j : Fin 3),
        C.vertexOfCorner Set.univ (f, j) = a ∧ N.normal f = x} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    let p := c.point (cyclicRunStart (linkNormals N c) count i)
    exact ⟨p.val.1.1, p.val.1.2, p.property, rfl⟩
  · rintro ⟨f, j, at_a, rfl⟩
    obtain ⟨k, hk⟩ := (C.linkCornerEquiv Set.univ a c covers).surjective ⟨(f, j), at_a⟩
    have eq := congrArg (fun p : C.CornerAt Set.univ a => p.val.1) hk
    obtain ⟨i, hi⟩ := exists_cyclicRunStart_label (linkNormals N c) count k
    exact ⟨i, hi.trans (congrArg N.normal eq)⟩

end Unfoldings.SpatialFolding.ConvexBoundary
