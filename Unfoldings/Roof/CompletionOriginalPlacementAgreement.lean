module

public import Unfoldings.Roof.CompletionOriginalLocalSeparation
public import Unfoldings.Roof.DevelopmentCoordinates

/-! Normalize an actual roof development to agree with every original whole-face placement. -/

@[expose] public section

noncomputable section



namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalPlacementIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
/-- One global normalization makes every original fine-face chart agree with its actual
original containing-face chart, including all edge and vertex copies. -/
theorem exists_development_agreeing_original_placements
    (retain : Set C.Seam) [PreconnectedSpace (C.Realization retain)]
    (fineRetain : Set L.partition.pairedComplex.Seam)
    (D : FacewiseDevelopment L.partition.pairedComplex fineRetain)
    (inclusion : L.originalRetain retain ⊆
      L.partition.pairedComplex.restrictRetain L.originalPieceSet fineRetain)
    (E : FacewiseDevelopment C retain) :
    ∃ A : FacewiseDevelopment L.partition.pairedComplex fineRetain,
      ∀ i : L.originalPieceSet, ∀ p : Plane,
        A.projectedPlacement L.cap i.val p =
          E.roofPlacement K (L.originalParent i) p := by
  let S := L.originalSubdivision
  let H := L.originalSubdivision_conforming retain
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
  let x := (L.pieceProjection (i.val)).symm p
  have projected : L.pieceProjection (i.val) x = p :=
    (L.pieceProjection (i.val)).apply_symm_apply p
  have roof_projected :
      L.cap.projectFace i.val x = p :=
    (L.partition.normalizedCap_projectFace L.conforming L.interior_nonempty i.val x).trans projected
  calc
    _ = A.place i.val x := by rw [← roof_projected, A.projectedPlacement_apply]
    _ = E.place (L.originalParent i) (S.place i x) := by rw [places]; rfl
    _ = E.roofPlacement K (L.originalParent i)
        (K.projectFace (L.originalParent i) (S.place i x)) :=
      (E.roofPlacement_apply K (L.originalParent i) (S.place i x)).symm
    _ = _ := congrArg (E.roofPlacement K (L.originalParent i))
      ((L.originalPlace_projection i.val (L.originalParent i)
        (L.originalParent_contains i) x).trans projected)

open Classical in
/-- Actual closed-face contact identification passes through the exact original subdivision. -/
theorem original_contact_of_local_roof_contact
    {retain : Set C.Seam} {fineRetain : Set L.partition.pairedComplex.Seam}
    (D : FacewiseDevelopment L.partition.pairedComplex fineRetain)
    (E : FacewiseDevelopment C retain)
    (agree : ∀ i : L.originalPieceSet, ∀ p : Plane,
      D.projectedPlacement L.cap i.val p =
        E.roofPlacement K (L.originalParent i) p)
    (U : Set Plane) (cover : K.footprint ⊆ U)
    (center : Plane) (exception : Set ℝ)
    (contacts : let Q := L.cap
      ∀ f g (p q : Plane),
        p ∈ (Q.projectedTriangle f).carrier ∩ U →
        q ∈ (Q.projectedTriangle g).carrier ∩ U →
        0 < ‖D.projectedPlacement Q f p - center‖ →
        ‖D.projectedPlacement Q f p - center‖ ∉ exception →
        D.projectedPlacement Q f p = D.projectedPlacement Q g q → p = q)
    (f g : Face) {p q : Plane}
    (first : p ∈ (K.projectedTriangle f).carrier)
    (last : q ∈ (K.projectedTriangle g).carrier)
    (positive : 0 < ‖E.roofPlacement K f p - center‖)
    (outside : ‖E.roofPlacement K f p - center‖ ∉ exception)
    (same : E.roofPlacement K f p = E.roofPlacement K g q) : p = q := by
  let Q := L.cap
  obtain ⟨a, first_parent, first_piece⟩ := L.original_piece_cover f p first
  obtain ⟨b, last_parent, last_piece⟩ := L.original_piece_cover g q last
  have first_Q : p ∈ (Q.projectedTriangle a.val).carrier :=
    (L.partition.normalizedCap_projectedTriangle_carrier L.conforming
      L.interior_nonempty a.val).symm ▸
      first_piece
  have last_Q : q ∈ (Q.projectedTriangle b.val).carrier :=
    (L.partition.normalizedCap_projectedTriangle_carrier L.conforming
      L.interior_nonempty b.val).symm ▸
      last_piece
  have first_U : p ∈ U := cover (K.footprint_eq_union_projectedTriangles.symm ▸
    Set.mem_iUnion.mpr ⟨f, first⟩)
  have last_U : q ∈ U := cover (K.footprint_eq_union_projectedTriangles.symm ▸
    Set.mem_iUnion.mpr ⟨g, last⟩)
  have first_value : D.projectedPlacement Q a.val p = E.roofPlacement K f p := by
    rw [agree a p, first_parent]
  have last_value : D.projectedPlacement Q b.val q = E.roofPlacement K g q := by
    rw [agree b q, last_parent]
  apply contacts a.val b.val p q ⟨first_Q, first_U⟩ ⟨last_Q, last_U⟩
  · rwa [first_value]
  · rwa [first_value]
  · rw [first_value, last_value]
    exact same

end Unfoldings.ConvexRoof.CompletionMesh
