module

public import Unfoldings.Cap.ClipOriginalRetention

/-! All fine copies of a point within one original face remain intrinsically identified. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalCopiesIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
def originalPointCopy (retain : Set C.Seam) (i : L.originalPieceSet) (p : Plane)
    (member : p ∈ (L.partition.projectedTriangle i.val).carrier) :
    L.originalComplex.Realization (L.originalRetain retain) :=
  L.originalComplex.faceMap (L.originalRetain retain) i
    ⟨(K.projectFaceEquiv (L.partition.face i.val)).symm p,
      (L.partition.triangle_carrier i.val).symm.subset ⟨p, member, rfl⟩⟩

open Classical in
theorem originalPointCopy_eq_across_seam (retain : Set C.Seam)
    (s : L.originalComplex.Seam) (kept : s ∈ L.originalRetain retain) {p : Plane}
    (member : p ∈ (L.partition.projectedTriangle (L.originalComplex.left s).face.val).edge
      (L.originalComplex.left s).edge) :
    L.originalPointCopy retain (L.originalComplex.left s).face p
        ((L.partition.projectedTriangle _).edge_subset _ member) =
      L.originalPointCopy retain (L.originalComplex.right s).face p
        ((L.partition.projectedTriangle _).edge_subset _
          ((L.partition.paired_seam_projected_edge s.val).subset member)) := by
  let a := L.originalComplex.left s
  let b := L.originalComplex.right s
  let x := (L.partition.edgeProjection a.face.val a.edge).symm ⟨p, member⟩
  have first_value : x.val = (K.projectFaceEquiv (L.partition.face a.face.val)).symm p := rfl
  have projected : K.projectFace (L.partition.face b.face.val)
      (L.originalComplex.identify s x).val = p := by
    exact (L.partition.paired_seam_projection s.val x).trans
      ((K.projectFaceEquiv (L.partition.face a.face.val)).apply_symm_apply p)
  have last_value : (L.originalComplex.identify s x).val =
      (K.projectFaceEquiv (L.partition.face b.face.val)).symm p := by
    apply (K.projectFaceEquiv (L.partition.face b.face.val)).injective
    exact projected.trans
      ((K.projectFaceEquiv (L.partition.face b.face.val)).apply_symm_apply p).symm
  have equal := L.originalComplex.seam_identified (L.originalRetain retain) s kept x
  change L.originalComplex.faceMap (L.originalRetain retain) a.face ⟨x.val, _⟩ =
    L.originalComplex.faceMap (L.originalRetain retain) b.face
      ⟨(L.originalComplex.identify s x).val, _⟩ at equal
  simpa only [originalPointCopy, first_value, last_value] using equal

open Classical in
theorem originalPointCopy_eq_of_shared_edge_same_parent (retain : Set C.Seam)
    {i j : L.originalPieceSet} (parent : L.originalParent i = L.originalParent j)
    (e f : Fin 3)
    (same : (L.partition.projectedTriangle i.val).edge e =
      (L.partition.projectedTriangle j.val).edge f)
    {p : Plane} (member : p ∈ (L.partition.projectedTriangle i.val).edge e) :
    L.originalPointCopy retain i p ((L.partition.projectedTriangle i.val).edge_subset e member) =
      L.originalPointCopy retain j p
        ((L.partition.projectedTriangle j.val).edge_subset f (same ▸ member)) := by
  by_cases equal : i = j
  · subst j
    rfl
  have different : i.val ≠ j.val := fun h => equal (Subtype.ext h)
  obtain ⟨s, ⟨first, last⟩ | ⟨first, last⟩⟩ := L.partition.pairedComplex_complete
    (a := ⟨i.val, e⟩) (b := ⟨j.val, f⟩) different same
  · let t : L.originalComplex.Seam := ⟨s, by simpa only [first, last] using
        (And.intro i.property j.property)⟩
    have first' : L.originalComplex.left t = ⟨i, e⟩ := by
      have face := congrArg EdgeRef.face first
      have edge := congrArg EdgeRef.edge first
      change EdgeRef.mk _ _ = EdgeRef.mk _ _
      congr 1
      exact Subtype.ext face
    have last' : L.originalComplex.right t = ⟨j, f⟩ := by
      have face := congrArg EdgeRef.face last
      have edge := congrArg EdgeRef.edge last
      change EdgeRef.mk _ _ = EdgeRef.mk _ _
      congr 1
      exact Subtype.ext face
    have kept : t ∈ L.originalRetain retain := L.original_seam_kept_of_same_parent retain t
      (by simpa only [first', last'] using parent)
    have on_left : p ∈ (L.partition.projectedTriangle
        (L.originalComplex.left t).face.val).edge (L.originalComplex.left t).edge := by
      simpa only [first'] using member
    simpa only [first', last'] using L.originalPointCopy_eq_across_seam retain t kept on_left
  · let t : L.originalComplex.Seam := ⟨s, by simpa only [first, last] using
        (And.intro j.property i.property)⟩
    have first' : L.originalComplex.left t = ⟨j, f⟩ := by
      have face := congrArg EdgeRef.face first
      have edge := congrArg EdgeRef.edge first
      change EdgeRef.mk _ _ = EdgeRef.mk _ _
      congr 1
      exact Subtype.ext face
    have last' : L.originalComplex.right t = ⟨i, e⟩ := by
      have face := congrArg EdgeRef.face last
      have edge := congrArg EdgeRef.edge last
      change EdgeRef.mk _ _ = EdgeRef.mk _ _
      congr 1
      exact Subtype.ext face
    have kept : t ∈ L.originalRetain retain := L.original_seam_kept_of_same_parent retain t
      (by simpa only [first', last'] using parent.symm)
    have on_left : p ∈ (L.partition.projectedTriangle
        (L.originalComplex.left t).face.val).edge (L.originalComplex.left t).edge := by
      simpa only [first'] using (same ▸ member)
    simpa only [first', last'] using
      (L.originalPointCopy_eq_across_seam retain t kept on_left).symm

open Classical in
theorem originalPointCopy_eq_of_same_parent (lower : Z < 0) (retain : Set C.Seam)
    {i j : L.originalPieceSet} (parent : L.originalParent i = L.originalParent j)
    (p : Plane) (first : p ∈ (L.partition.projectedTriangle i.val).carrier)
    (last : p ∈ (L.partition.projectedTriangle j.val).carrier) :
    L.originalPointCopy retain i p first = L.originalPointCopy retain j p last := by
  let f := L.originalParent i
  let I := {a : L.originalPieceSet // L.originalParent a = f}
  let triangle (a : I) := L.partition.projectedTriangle a.val.val
  have cover : (⋃ a : I, (triangle a).carrier) = (K.projectedTriangle f).carrier := by
    apply Set.Subset.antisymm
    · intro q member
      obtain ⟨a, member⟩ := Set.mem_iUnion.mp member
      simpa only [a.property] using L.originalParent_contains a.val member
    · intro q member
      obtain ⟨a, at_parent, inside⟩ := L.original_piece_cover lower f q member
      exact Set.mem_iUnion.mpr ⟨⟨a, at_parent⟩, inside⟩
  have conforming : TriangleFamily.Conforming triangle := by
    intro a b different q member
    exact L.conforming a.val.val b.val.val
      (fun same => different (Subtype.ext (Subtype.ext same))) q member
  have separated : Pairwise (fun a b : I =>
      Disjoint (interior (triangle a).carrier) (interior (triangle b).carrier)) := by
    intro a b different
    exact L.partition.separated (fun same => different (Subtype.ext (Subtype.ext same)))
  let value (a : {a : I // p ∈ (triangle a).carrier}) :=
    L.originalPointCopy retain a.val.val p a.property
  apply TriangleFamily.incident_values_eq triangle (K.projectedTriangle f).convex_carrier
    cover conforming separated p value ?_
      ⟨⟨i, rfl⟩, first⟩ ⟨⟨j, parent.symm⟩, last⟩
  intro a b e g same member
  exact L.originalPointCopy_eq_of_shared_edge_same_parent retain
    (a.val.property.trans b.val.property.symm) e g same member

end Unfoldings.ConvexCap.LineAlignedClip
