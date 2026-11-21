module

public import Unfoldings.Cap.RefinementCurvatureSupport
public import Unfoldings.Cap.JordanBankPositions
public import Unfoldings.Cap.SharpRestrictedSectionSum
public import Unfoldings.Geometry.ShortOrientedFan
public import Unfoldings.Geometry.LineTransverse

/-! A straight connector avoiding old vertices meets only flat faces and transverse creases. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

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

open Classical in
/-- Every contour contact on a connector through no old vertex has regular
incident slopes. The line may cross old edges. -/
theorem regular_jordan_sectionSlopes_of_avoids_old_vertices
    {I : Type*} (original : I → Triangle) (conforming : TriangleFamily.Conforming original)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (original i).carrier) (interior (original j).carrier)))
    (slope : I → Plane) (height : I → Plane → ℝ) (parent : Face → I)
    (inside : ∀ f, (K.projectedTriangle f).carrier ⊆ (original (parent f)).carrier)
    (normal_eq : ∀ f, K.normalSlope f = slope (parent f))
    (affine : ∀ i x y, height i x - height i y = -inner ℝ (slope i) (x - y))
    (agree : ∀ i j x, x ∈ (original i).carrier → x ∈ (original j).carrier →
      height i x = height j x)
    {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    {a b : Plane} (different : a ≠ b)
    (contact : K.jordanBankPosition jordan contains avoids i ∈ segment ℝ a b)
    (regular : ∀ (t : ℝ) (j : I) (k : Fin 3),
      AffineMap.lineMap a b t ≠ (original j).vertex k) :
    K.HasRegularSectionSlopes ((K.jordanContourVertexEquiv jordan contains avoids) i).val
      (b - a) := by
  obtain ⟨t, _, point⟩ := (segment_eq_image_lineMap ℝ a b).le contact
  rw [K.jordanBankPosition_eq_projectedVertex jordan contains avoids i] at point
  exact K.exists_transverse_incidentSlopes_of_regular_line original conforming separated slope
    height parent inside normal_eq affine agree _ different t point regular

end Unfoldings.ConvexCap
