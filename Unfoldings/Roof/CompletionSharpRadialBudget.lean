module

public import Unfoldings.Roof.CompletionSharpCorners
public import Unfoldings.Cap.RadialSharpBankBudget

/-! The sharp radial-bank estimate on the actual line-aligned completion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

/-- One closure corner is either inside an old face or lies inside an old
edge with a local bank ray along the edge. -/
def RegularClosingCorner (J : Set Plane) (p : Plane) : Prop :=
  (∃ old, p ∈ interior (E.mesh.projectedTriangle old).carrier) ∨
    ∃ (old : E.mesh.Index) (edge : Fin 3) (k : ℝ) (closing : Plane),
      p ∈ (E.mesh.projectedTriangle old).edge edge ∧
      ¬ (E.mesh.projectedTriangle old).IsVertex p ∧
      (∀ᶠ x in 𝓝 p, x ∈ J → x - p ∈
        nonnegativeRay (k • ((E.mesh.projectedTriangle old).vertex (Triangle.next edge) -
          (E.mesh.projectedTriangle old).vertex edge)) ∪ nonnegativeRay closing)

open Classical in
/-- The three straight links and the three one-face corner charges are
derived from geometric regularity of the old completion, in the mesh
refined along the actual closure lines. -/
theorem alignToLines_sharp_radial_bank_bound {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0)
    {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
    (initial : 0 < dist q (P.vertex 0))
    (progress : dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)))
    (height : Plane →ₗ[ℝ] ℝ) (first : 0 ≤ height (P.vertex 0 - q))
    (last : 0 ≤ height (P.vertex (Fin.last n) - q)) (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)))
    (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (height_bound : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (sin φ / 2) i).normal 2)
    (corners_regular : ∀ p, p = P.vertex 0 ∨ p = P.vertex (Fin.last n) ∨ p = c →
      E.RegularClosingCorner (P.threeSegmentClosure q c) p)
    (links_regular : ∀ (j : Fin 3) (t : ℝ) (f : E.mesh.Index) (k : Fin 3),
      let link := radialClosingLinks q (P.vertex 0) (P.vertex (Fin.last n)) c j
      AffineMap.lineMap link.1 link.2 t ≠ (E.mesh.projectedTriangle f).vertex k) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    L.cap.TiltBound φ → ∀ (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
      (inside : P.threeSegmentClosure q c ⊆ interior L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier)
        (P.threeSegmentClosure q c)),
      let contains := inside.trans interior_subset
      |∑ i ∈ L.cap.jordanGeometricBankIndices jordan contains avoids (Set.range P.path)
          (radialClosingCorners q (P.vertex 0) (P.vertex (Fin.last n)) c),
        L.cap.jordanContourTurnError jordan contains avoids i| ≤
          shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let J := P.threeSegmentClosure q c
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  exact fun tilt jordan inside avoids => by
    let contains := inside.trans interior_subset
    apply L.cap.abs_radial_bank_turn_error_le_sharp_of_regular_links P q c jordan contains avoids
      inside initial progress height first last outside outward nonnegative small tilt
    · intro i named
      let p := L.cap.jordanBankPosition jordan contains avoids i
      change p = a ∨ p = b ∨ p = c at named
      rcases corners_regular p named with ⟨old, belongs⟩ | ⟨old, edge, k, d, on_edge, away, local_rays⟩
      · exact E.alignToLines_sharp_corner_in_old_face equation proper old nonnegative small
          height_bound tilt jordan contains inside avoids i belongs
      · exact E.alignToLines_sharp_corner_on_old_edge equation proper old edge nonnegative small
          height_bound tilt jordan contains inside avoids i on_edge away k d local_rays
    · intro j i contact _ _
      let link := radialClosingLinks q a b c j
      have different := radialClosingLinks_different q a b c initial height outside outward j
      exact E.alignToLines_regular_jordan_sectionSlopes equation proper different
        (links_regular j) jordan contains avoids i contact

end Unfoldings.ConvexRoof.CompletionMesh
