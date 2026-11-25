module

public import Unfoldings.Roof.CompletionAcuteCorners

/-! Turn budgets for the physical completion aligned to one or both acute closing disks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

open Classical in
/-- Local regularity of the old mesh gives the sharp geometric bank turn
bound in a completion refined along the actual closing lines. -/
theorem alignToLines_acute_bank_bound {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0)
    {n : ℕ} (P : PolygonalChain Plane (n + 1)) (c : Plane)
    (h k : Plane →L[ℝ] ℝ) (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))
    (initial : h c < h (P.vertex 0)) (terminal : k (P.vertex (Fin.last (n + 1))) < k c)
    (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (height_bound : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (sin φ / 2) i).normal 2)
    (corners : ∀ p ∈ P.twoClosingCorners c, E.RegularClosingCorner (P.twoLinkClosure c) p)
    (links_regular : ∀ (j : Fin 2) (t : ℝ) (f : E.mesh.Index) (i : Fin 3),
      let link := P.twoClosingLinks c j
      AffineMap.lineMap link.1 link.2 t ≠ (E.mesh.projectedTriangle f).vertex i) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    L.cap.TiltBound φ → ∀ (jordan : Schoenflies.IsJordanCurve (P.twoLinkClosure c))
      (inside : P.twoLinkClosure c ⊆ interior L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier) (P.twoLinkClosure c)),
      let contains := inside.trans interior_subset
      |∑ i ∈ L.cap.jordanGeometricBankIndices jordan contains avoids (Set.range P.path)
          (P.twoClosingCorners c),
        L.cap.jordanContourTurnError jordan contains avoids i| ≤ acuteConeDevelopmentHeading φ := by
  let L := E.alignToLines equation proper
  let : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite
  exact fun tilt jordan inside avoids => by
    let contains := inside.trans interior_subset
    apply L.cap.abs_acute_bank_turn_error_le_of_regular_links P c jordan contains avoids
      inside h k (Nat.succ_pos n) first last initial.le terminal.le nonnegative small tilt
    · intro i named
      let p := L.cap.jordanBankPosition jordan contains avoids i
      rcases corners p named with ⟨old, member⟩ | ⟨old, edge, a, d, member, away, local_rays⟩
      · exact E.alignToLines_sharp_corner_in_old_face equation proper old nonnegative small
          height_bound tilt jordan contains inside avoids i member
      · exact E.alignToLines_sharp_corner_on_old_edge equation proper old edge nonnegative small
          height_bound tilt jordan contains inside avoids i member away a d local_rays
    · intro j i contact _ _
      let link := P.twoClosingLinks c j
      have different : link.1 ≠ link.2 := by
        fin_cases j
        · intro eq
          change P.vertex (Fin.last (n + 1)) = c at eq
          exact terminal.ne (congrArg k eq)
        · intro eq
          change c = P.vertex 0 at eq
          exact initial.ne (congrArg h eq)
      exact E.alignToLines_regular_jordan_sectionSlopes equation proper different
        (links_regular j) jordan contains avoids i contact

end Unfoldings.ConvexRoof.CompletionMesh
