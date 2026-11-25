module

public import Unfoldings.Roof.SharpRestrictedSection
public import Unfoldings.Roof.Boundary
public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Geometry.LineTransverse
public import Unfoldings.Geometry.ShortOrientedFan
public import Unfoldings.Geometry.ConformingPointMultiplicity

/-! Generic connector contacts and one shared budget across a two-link closing path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- At a generic refined contact, the two possible support slopes can be
chosen equal in a flat region or transverse to the connector at a crease. -/
theorem exists_transverse_incidentSlopes_of_regular_line
    {I : Type*} (original : I → Triangle) (conforming : TriangleFamily.Conforming original)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (original i).carrier) (interior (original j).carrier)))
    (slope : I → Plane) (height : I → Plane → ℝ) (parent : Face → I)
    (inside : ∀ f, (K.projectedTriangle f).carrier ⊆ (original (parent f)).carrier)
    (normal_eq : ∀ f, K.normalSlope f = slope (parent f))
    (affine : ∀ i x y, height i x - height i y = -inner ℝ (slope i) (x - y))
    (agree : ∀ i j x, x ∈ (original i).carrier → x ∈ (original j).carrier →
      height i x = height j x)
    (v : C.Vertex Set.univ) {p q : Plane} (different : p ≠ q) (t : ℝ)
    (at_contact : AffineMap.lineMap p q t = K.projectedVertex v)
    (regular : ∀ (r : ℝ) (i : I) (k : Fin 3), AffineMap.lineMap p q r ≠ (original i).vertex k) :
    ∃ a b : Plane,
      (∀ f k, C.vertexOfCorner Set.univ (f, k) = v → K.normalSlope f = a ∨ K.normalSlope f = b) ∧
      (a = b ∨ inner ℝ (a - b) (q - p) ≠ 0) := by
  classical
  let z := K.projectedVertex v
  have away (i : I) : ¬ (original i).IsVertex z := by
    rintro ⟨k, eq⟩
    exact regular t i k (at_contact.trans eq.symm)
  have member (f : Face) (i : Fin 3) (eq : C.vertexOfCorner Set.univ (f, i) = v) :
      z ∈ (original (parent f)).carrier := by
    have h := inside f ((K.projectedTriangle f).vertex_mem i)
    rw [← K.projectedVertex_ofCorner, eq] at h
    exact h
  obtain ⟨⟨f, k⟩, hk⟩ := C.vertexOfCorner_surjective Set.univ v
  let i := parent f
  by_cases other : ∃ j, j ≠ i ∧ z ∈ (original j).carrier
  · obtain ⟨j, ij, hj⟩ := other
    obtain ⟨other, all⟩ := TriangleFamily.atMostTwo_faces_of_nonvertex original conforming
      separated i (member f k hk) (away i)
    have same : j = other := (all j hj).resolve_left ij
    have choices (g : Face) (l : Fin 3) (hl : C.vertexOfCorner Set.univ (g, l) = v) :
        K.normalSlope g = slope i ∨ K.normalSlope g = slope j := by
      rw [normal_eq, same]
      exact (all (parent g) (member g l hl)).imp (congrArg slope) (congrArg slope)
    refine ⟨slope i, slope j, choices, ?_⟩
    by_cases equal : slope i = slope j
    · exact Or.inl equal
    · apply Or.inr
      obtain ⟨e, d, same_edge, on_edge⟩ :=
        (conforming i j (Ne.symm ij) z ⟨member f k hk, hj⟩).resolve_left
          (fun hh => away i hh.1)
      let x := (original i).vertex e
      let y := (original i).vertex (Triangle.next e)
      have xedge : x ∈ (original i).edge e := left_mem_segment ℝ _ _
      have yedge : y ∈ (original i).edge e := right_mem_segment ℝ _ _
      have xj : x ∈ (original j).edge d := same_edge ▸ xedge
      have yj : y ∈ (original j).edge d := same_edge ▸ yedge
      have hx := agree i j x ((original i).edge_subset _ xedge)
        ((original j).edge_subset _ xj)
      have hy := agree i j y ((original i).edge_subset _ yedge)
        ((original j).edge_subset _ yj)
      have tied : inner ℝ (slope i - slope j) (y - x) = 0 := by
        rw [inner_sub_left]
        linarith only [hx, hy, affine i y x, affine j y x]
      have side : orient 0 (y - x) (q - p) ≠ 0 :=
        line_transverse_of_avoids_endpoint ((original i).edge_endpoints_ne e) different
          (fun a => regular a i e) t (by
            rw [at_contact]
            exact orient_eq_zero_of_mem_segment on_edge)
      intro forbidden
      exact side (orient_zero_of_orthogonal_pair (sub_ne_zero.mpr equal) tied forbidden)
  · refine ⟨slope i, slope i, ?_, Or.inl rfl⟩
    intro g l hl
    have same : parent g = i := by
      by_contra different
      exact other ⟨parent g, different, member g l hl⟩
    exact Or.inl ((normal_eq g).trans (congrArg slope same))

/-- The incident slopes come from one plane or two planes transverse to the section. -/
def HasRegularSectionSlopes (w : C.Vertex Set.univ) (direction : Plane) : Prop :=
  ∃ a b : Plane,
    (∀ f i, C.vertexOfCorner Set.univ (f, i) = w → K.normalSlope f = a ∨ K.normalSlope f = b) ∧
    (a = b ∨ inner ℝ (a - b) direction ≠ 0)

open Classical in
/-- The actual sector at each interior contact of one straight closing link. -/
structure RegularClosingLink (faces : Set Face) (origin direction : Plane) (I : Type*) where
  bank : I → (C.restrictFaces faces).BoundaryEnd Set.univ
  time : I → ℝ
  distinct : Function.Injective time
  position : ∀ i, Cap.horizontal ((K.folding.restrictFaces faces).boundaryPosition (bank i)) =
    origin + time i • direction
  inside : ∀ i, origin + time i • direction ∈ interior K.footprint
  outgoing : I → ℝ
  incoming : I → ℝ
  opposite : ∀ i, outgoing i * incoming i < 0
  outgoing_ray : ∀ i, Cap.horizontal ((K.folding.restrictFaces faces).germDirection (bank i).val) =
    outgoing i • direction
  incoming_ray : ∀ i, Cap.horizontal ((K.folding.restrictFaces faces).germDirection
    ((C.restrictFaces faces).boundaryMate Set.univ (bank i)).val) = incoming i • direction
  regular : ∀ i, K.HasRegularSectionSlopes (C.includeRestrictedVertexUniv faces
    ((C.restrictFaces faces).boundaryEndVertex Set.univ (bank i))) direction

namespace RegularClosingLink

variable {K} {faces : Set Face} {origin direction : Plane} {I : Type*}

open Classical in
/-- The actual face on each side of a section contact. -/
def contactFace (L : K.RegularClosingLink faces origin direction I) (i : I) (side : Bool) : Face :=
  if side then ((C.restrictFaces faces).boundaryMate Set.univ (L.bank i)).val.1.1.val
  else (L.bank i).val.1.1.val

open Classical in
theorem contactFace_active (L : K.RegularClosingLink faces origin direction I) (i : I) (side : Bool) :
    K.supportHeight (L.contactFace i side) (origin + L.time i • direction) =
      K.roofHeight (origin + L.time i • direction) := by
  let R := C.restrictFaces faces
  have active (p : R.BoundaryEnd Set.univ) :
      K.supportHeight p.val.1.1.val (Cap.horizontal ((K.folding.restrictFaces faces).boundaryPosition p)) =
        K.roofHeight (Cap.horizontal ((K.folding.restrictFaces faces).boundaryPosition p)) := by
    rw [(K.folding.restrictFaces faces).boundaryPosition_raw]
    exact (K.supportHeight_face p.val.1.1.val ((C.triangle p.val.1.1.val).vertex p.val.1.2)).trans
      (K.roofHeight_face p.val.1.1.val
        ⟨(C.triangle p.val.1.1.val).vertex p.val.1.2, (C.triangle _).vertex_mem p.val.1.2⟩).symm
  rw [← L.position i]
  cases side
  · exact active (L.bank i)
  · change K.supportHeight (R.boundaryMate Set.univ (L.bank i)).val.1.1.val _ = _
    have at_mate := active (R.boundaryMate Set.univ (L.bank i))
    rw [show (K.folding.restrictFaces faces).boundaryPosition (R.boundaryMate Set.univ (L.bank i)) =
      (K.folding.restrictFaces faces).boundaryPosition (L.bank i) from
      (K.folding.restrictFaces faces).boundaryPosition_mate (L.bank i)] at at_mate
    exact at_mate

open Classical in
/-- The actual turn error of one regular straight contact is bounded by the
sine-scaled bend of its two active support directions. -/
theorem abs_turnError_le (L : K.RegularClosingLink faces origin direction I)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) (i : I) :
    |K.restrictedBoundaryTurnError faces (L.bank i)| ≤ sin φ *
      angle (K.sectionDirection (L.contactFace i false) direction)
        (K.sectionDirection (L.contactFace i true) direction) := by
  let R := C.restrictFaces faces
  let p := L.bank i
  let w := C.includeRestrictedVertexUniv faces (R.boundaryEndVertex Set.univ p)
  have position : K.projectedVertex w = origin + L.time i • direction := by
    change K.projectedVertex (C.vertexOfCorner Set.univ (p.val.1.1.val, p.val.1.2)) = _
    rw [K.projectedVertex_ofCorner]
    have h := L.position i
    rw [(K.folding.restrictFaces faces).boundaryPosition_raw] at h
    exact h
  have internal := (K.projectedVertex_mem_interior_iff w).mp (by rw [position]; exact L.inside i)
  obtain ⟨a, b, slopes, transverse⟩ := L.regular i
  change _ ≤ sin φ * angle (K.sectionDirection p.val.1.1.val direction)
    (K.sectionDirection (R.boundaryMate Set.univ p).val.1.1.val direction)
  rcases mul_neg_iff.mp (L.opposite i) with ⟨positive, negative⟩ | ⟨negative, positive⟩
  · exact K.abs_restrictedBoundaryTurnError_le_sin_mul_active_angle nonnegative small tilt faces
      p direction a b internal slopes transverse positive (neg_pos.mpr negative) (L.outgoing_ray i)
      (by rw [neg_smul, smul_neg, neg_neg]; exact L.incoming_ray i)
  · have reversed : a = b ∨ inner ℝ (a - b) (-direction) ≠ 0 := by
      rw [inner_neg_right, neg_ne_zero]
      exact transverse
    have h := K.abs_restrictedBoundaryTurnError_le_sin_mul_active_angle nonnegative small tilt faces
      p (-direction) a b internal slopes reversed (neg_pos.mpr negative) positive
      (by rw [neg_smul, smul_neg, neg_neg]; exact L.outgoing_ray i)
      (by rw [neg_neg]; exact L.incoming_ray i)
    rwa [K.sectionDirection_neg, K.sectionDirection_neg, angle_neg_neg] at h

end RegularClosingLink

open Classical in
/-- Both actual straight links of a closing path share the same tilt allowance.
The orientation of each boundary fan may be chosen independently. -/
theorem sum_abs_restricted_closing_errors_le {I J : Type*} [Fintype I] [Fintype J]
    {faces : Set Face} (origin d e : Plane) (d_unit : ‖d‖ = 1) (e_unit : ‖e‖ = 1)
    (bendTime : ℝ) (middle : Face)
    (bend_active : K.supportHeight middle (origin + bendTime • d) =
      K.roofHeight (origin + bendTime • d))
    (first : K.RegularClosingLink faces origin d I)
    (last : K.RegularClosingLink faces (origin + bendTime • d) e J)
    (before : ∀ i, first.time i < bendTime) (after : ∀ j, 0 < last.time j)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i, |K.restrictedBoundaryTurnError faces (first.bank i)|) +
      (∑ j, |K.restrictedBoundaryTurnError faces (last.bank j)|) ≤
      sin φ * (2 * φ + tan φ * ‖d - e‖) := by
  have first_sum := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset I)) => first.abs_turnError_le nonnegative small tilt i)
  have last_sum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset J)) => last.abs_turnError_le nonnegative small tilt j)
  rw [← Finset.mul_sum] at first_sum last_sum
  have variation := K.sum_active_closing_angles_le origin d e d_unit e_unit bendTime middle bend_active
    first.time first.distinct before last.time last.distinct after first.contactFace last.contactFace
    first.contactFace_active last.contactFace_active nonnegative small tilt
  have sine : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos])
  exact (add_le_add first_sum last_sum).trans
    ((mul_add _ _ _).ge.trans (mul_le_mul_of_nonneg_left variation sine))

end Unfoldings.ConvexRoof
