module

public import Unfoldings.Cap.ClipOriginalLocalSeparation
public import Unfoldings.Cap.ClippedCapCoordinates

/-! Normalize an actual roof development to agree with every original whole-face placement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance clippedPlacementIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem normalizedCap_projectFace (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) (i : T.Index) (x : Plane) :
    (T.normalizedCap conforming lower).projectFace i x = K.projectFace (T.face i) x := by
  change Cap.horizontal (T.normalizedFolding.place i x) = _
  rw [T.normalized_place, horizontal_add_shift, T.horizontal_placement]

end Unfoldings.ConvexCap.ClipSpatialTriangles

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalPlacementIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
/-- One global normalization makes every original fine-face chart agree with its actual
original containing-face chart, including all edge and vertex copies. -/
theorem exists_development_agreeing_original_placements (lower : Z < 0)
    (retain : Set C.Seam) [PreconnectedSpace (C.Realization retain)]
    (fineRetain : Set L.partition.pairedComplex.Seam)
    (D : FacewiseDevelopment L.partition.pairedComplex fineRetain)
    (inclusion : L.originalRetain retain ⊆
      L.partition.pairedComplex.restrictRetain L.originalPieceSet fineRetain)
    (E : FacewiseDevelopment C retain) :
    ∃ A : FacewiseDevelopment L.partition.pairedComplex fineRetain,
      ∀ i : L.originalPieceSet, ∀ p : Plane,
        A.projectedPlacement (L.partition.normalizedCap L.conforming lower) i.val p =
          E.projectedPlacement K (L.originalParent i) p := by
  let S := L.originalSubdivision lower
  let H := L.originalSubdivision_conforming lower retain
  let : PreconnectedSpace (L.originalComplex.Realization (L.originalRetain retain)) :=
    H.metricEquiv.symm.surjective.denseRange.preconnectedSpace H.metricEquiv.symm.continuous
  obtain ⟨f⟩ := K.nonempty_face
  obtain ⟨root, _, _parent, _value⟩ := S.cover f
    ⟨(C.triangle f).vertex 0, (C.triangle f).vertex_mem 0⟩
  let A := D.normalize root.val (E.childPlace S root)
  let restriction : FacewiseDevelopment L.originalComplex (L.originalRetain retain) :=
    (A.restrictFaces L.originalPieceSet).cut inclusion
  have agree : restriction = E.subdivide S H :=
    restriction.eq_of_root (E.subdivide S H)
      (L.originalComplex.duallyConnected_of_preconnected (L.originalRetain retain)) root
      (D.normalize_root root.val (E.childPlace S root))
  have places (i : L.originalPieceSet) : A.place i.val = E.childPlace S i :=
    congrArg (fun development => development.place i) agree
  refine ⟨A, ?_⟩
  intro i p
  let x := (K.projectFaceEquiv (L.partition.face i.val)).symm p
  have projected : K.projectFace (L.partition.face i.val) x = p :=
    (K.projectFaceEquiv (L.partition.face i.val)).apply_symm_apply p
  have roof_projected :
      (L.partition.normalizedCap L.conforming lower).projectFace i.val x = p :=
    (L.partition.normalizedCap_projectFace L.conforming lower i.val x).trans projected
  calc
    _ = A.place i.val x := by rw [← roof_projected, A.projectedPlacement_apply]
    _ = E.place (L.originalParent i) (S.place i x) := by rw [places]; rfl
    _ = E.projectedPlacement K (L.originalParent i)
        (K.projectFace (L.originalParent i) (S.place i x)) :=
      (E.projectedPlacement_apply K (L.originalParent i) (S.place i x)).symm
    _ = _ := congrArg (E.projectedPlacement K (L.originalParent i))
      ((L.partition.originalPlace_projection i.val (L.originalParent i)
        (L.originalParent_contains i) x).trans projected)

open Classical in
/-- Actual closed-face contact identification passes through the exact original subdivision. -/
theorem original_contact_of_local_roof_contact (lower : Z < 0)
    {retain : Set C.Seam} {fineRetain : Set L.partition.pairedComplex.Seam}
    (D : FacewiseDevelopment L.partition.pairedComplex fineRetain)
    (E : FacewiseDevelopment C retain)
    (agree : ∀ i : L.originalPieceSet, ∀ p : Plane,
      D.projectedPlacement (L.partition.normalizedCap L.conforming lower) i.val p =
        E.projectedPlacement K (L.originalParent i) p)
    (U : Set Plane) (cover : K.footprint ⊆ U)
    (center : Plane) (exception : Set ℝ)
    (contacts : let Q := L.partition.normalizedCap L.conforming lower
      ∀ f g (p q : Plane),
        p ∈ (Q.projectedTriangle f).carrier ∩ U →
        q ∈ (Q.projectedTriangle g).carrier ∩ U →
        0 < ‖D.projectedPlacement Q f p - center‖ →
        ‖D.projectedPlacement Q f p - center‖ ∉ exception →
        D.projectedPlacement Q f p = D.projectedPlacement Q g q → p = q)
    (f g : Face) {p q : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier)
    (last : q ∈ (K.projectedTriangle g).carrier)
    (positive : 0 < ‖E.projectedPlacement K f p - center‖)
    (outside : ‖E.projectedPlacement K f p - center‖ ∉ exception)
    (same : E.projectedPlacement K f p = E.projectedPlacement K g q) : p = q := by
  let Q := L.partition.normalizedCap L.conforming lower
  obtain ⟨a, first_parent, first_piece⟩ := L.original_piece_cover lower f p first
  obtain ⟨b, last_parent, last_piece⟩ := L.original_piece_cover lower g q last
  have first_Q : p ∈ (Q.projectedTriangle a.val).carrier :=
    (L.partition.normalizedCap_projectedTriangle_carrier L.conforming lower a.val).symm ▸
      first_piece
  have last_Q : q ∈ (Q.projectedTriangle b.val).carrier :=
    (L.partition.normalizedCap_projectedTriangle_carrier L.conforming lower b.val).symm ▸
      last_piece
  have first_U : p ∈ U := cover (K.footprint_eq_union_projectedTriangles.symm ▸
    Set.mem_iUnion.mpr ⟨f, first⟩)
  have last_U : q ∈ U := cover (K.footprint_eq_union_projectedTriangles.symm ▸
    Set.mem_iUnion.mpr ⟨g, last⟩)
  have first_value : D.projectedPlacement Q a.val p = E.projectedPlacement K f p := by
    rw [agree a p, first_parent]
  have last_value : D.projectedPlacement Q b.val q = E.projectedPlacement K g q := by
    rw [agree b q, last_parent]
  apply contacts a.val b.val p q ⟨first_Q, first_U⟩ ⟨last_Q, last_U⟩
  · rwa [first_value]
  · rwa [first_value]
  · rw [first_value, last_value]
    exact same

end Unfoldings.ConvexCap.LineAlignedClip
