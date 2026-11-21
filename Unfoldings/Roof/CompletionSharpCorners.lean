module

public import Unfoldings.Roof.CompletionRefinementCurvature
public import Unfoldings.Cap.RefinedCornerSlopes
public import Unfoldings.Cap.SharpJordanCorner

/-! The sharp corner bounds on literal refined completion meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

open Filter Topology Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra)

open Classical in
/-- A nonvertex old-edge corner may use the bank ray lying along that edge. -/
theorem alignToLines_sharp_corner_on_old_edge {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0)
    (old : E.mesh.Index) (edge : Fin 3)
    (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (height_bound : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (sin φ / 2) i).normal 2) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    L.cap.TiltBound φ → ∀ {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J)
      (contains : J ⊆ L.cap.footprint) (inside : J ⊆ interior L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier) J)
      (i : Fin ((L.cap.jordanContour jordan contains avoids).length + 1)),
      let p := L.cap.jordanBankPosition jordan contains avoids i
      let d := (E.mesh.projectedTriangle old).vertex (Triangle.next edge) -
        (E.mesh.projectedTriangle old).vertex edge
      p ∈ (E.mesh.projectedTriangle old).edge edge →
      ¬ (E.mesh.projectedTriangle old).IsVertex p →
      ∀ (k : ℝ) (closing : Plane),
        (∀ᶠ x in 𝓝 p, x ∈ J → x - p ∈ nonnegativeRay (k • d) ∪ nonnegativeRay closing) →
        |L.cap.jordanContourTurnError jordan contains avoids i| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let family := K.completionPlanes E.tentHeight (sin φ / 2)
  obtain ⟨parent, subordinate, normal_eq⟩ := E.alignToLines_parent_slopes equation proper
  let plane (j : E.mesh.Index) := family (E.mesh.support j)
  have affine (j : E.mesh.Index) (x y : Plane) :
      (plane j).height x - (plane j).height y = -inner ℝ (plane j).normalSlope (x - y) := by
    linarith only [(plane j).height_difference y x]
  have agree (i j : E.mesh.Index) (x : Plane)
      (hi : x ∈ (E.mesh.projectedTriangle i).carrier)
      (hj : x ∈ (E.mesh.projectedTriangle j).carrier) : (plane i).height x = (plane j).height x :=
    (E.mesh.active i x hi).symm.trans (E.mesh.active j x hj)
  have height (i : L.mesh.Index) : (3 : ℝ) / 4 ≤ L.cap.normal i 2 :=
    height_bound (L.mesh.support i)
  exact fun tilt {J} jordan contains inside avoids i on_edge away k closing locally => by
    have point := L.cap.jordanBankPosition_eq_projectedVertex jordan contains avoids i
    rw [point] at on_edge away
    obtain ⟨a, b, slopes, tangent⟩ :=
      L.cap.exists_tangent_incidentSlopes_on_old_edge E.mesh.projectedTriangle E.conforming
        E.mesh.separated (fun j => (plane j).normalSlope) (fun j => (plane j).height) parent
        subordinate normal_eq affine agree _ old edge on_edge away
    apply L.cap.abs_jordan_turn_error_le_sharp_of_local_crease_ray jordan contains avoids inside
      i slopes _ height locally nonnegative small tilt
    rw [real_inner_smul_right, tangent, mul_zero]

open Classical in
/-- A corner inside an old face has a single slope even if its refined fan
contains many smaller triangles. -/
theorem alignToLines_sharp_corner_in_old_face {A : Type u} [Finite A]
    (equation : A → Plane →ᵃ[ℝ] ℝ) (proper : ∀ a, equation a ≠ 0) (old : E.mesh.Index)
    (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (height_bound : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (sin φ / 2) i).normal 2) :
    let L := E.alignToLines equation proper
    letI := @Fintype.ofFinite _ L.mesh.finite
    L.cap.TiltBound φ → ∀ {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J)
      (contains : J ⊆ L.cap.footprint) (inside : J ⊆ interior L.cap.footprint)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier) J)
      (i : Fin ((L.cap.jordanContour jordan contains avoids).length + 1)),
      L.cap.jordanBankPosition jordan contains avoids i ∈
        interior (E.mesh.projectedTriangle old).carrier →
        |L.cap.jordanContourTurnError jordan contains avoids i| ≤ 2 * arcsin (tan (φ / 2) ^ 2) := by
  let L := E.alignToLines equation proper
  let := @Fintype.ofFinite _ L.mesh.finite
  let family := K.completionPlanes E.tentHeight (sin φ / 2)
  obtain ⟨parent, subordinate, normal_eq⟩ := E.alignToLines_parent_slopes equation proper
  let slope (j : E.mesh.Index) := (family (E.mesh.support j)).normalSlope
  have height (i : L.mesh.Index) : (3 : ℝ) / 4 ≤ L.cap.normal i 2 :=
    height_bound (L.mesh.support i)
  exact fun tilt {J} jordan contains inside avoids i member => by
    rw [L.cap.jordanBankPosition_eq_projectedVertex jordan contains avoids i] at member
    have flat := L.cap.refined_slope_eq_of_mem_old_interior E.mesh.projectedTriangle E.conforming
      slope parent subordinate normal_eq _ old member
    apply L.cap.abs_jordan_turn_error_le_sharp_of_crease_ray jordan contains avoids inside i
      (a := slope old) (b := slope old) (fun f k there => Or.inl (flat f k there))
      height nonnegative small tilt
    exact Or.inl (by rw [sub_self, inner_zero_left])

end Unfoldings.ConvexRoof.CompletionMesh
