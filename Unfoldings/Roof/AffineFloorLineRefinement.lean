module

public import Unfoldings.Roof.AffineFloorRoof
public import Unfoldings.Geometry.SpatialEnvelopeAlignment
public import Unfoldings.Geometry.ConstraintInteriors
public import Unfoldings.Roof.SharpClosingContacts
public import Unfoldings.Roof.CurvatureNormalInterior
public import Unfoldings.Geometry.SegmentVertices

/-! Refine the actual roof under an affine floor by proper lines with all supports unchanged. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  {A : Type u} (equation : A → Plane →ᵃ[ℝ] ℝ)

/-- The common mesh is a genuine subdivision of the coarse roof with the same
support at each fine face. -/
structure LineRefinement where
  mesh : FloorMesh family floor equation Z
  parent : mesh.Index → T.Index
  contained : ∀ f, (mesh.projectedTriangle f).carrier ⊆ (T.projectedTriangle (parent f)).carrier
  same_support : ∀ f, mesh.support f = T.support (parent f)

/-- Construct the common line refinement without changing the floor or any physical support. -/
def refineToLines [Finite A] (proper : ∀ a, equation a ≠ 0)
    (inside : (interior (clipAbove family floor Z)).Nonempty) : T.LineRefinement equation := by
  let : Fintype T.Index := @Fintype.ofFinite _ T.finite
  let : Fintype A := Fintype.ofFinite A
  let old := Fintype.equivFin T.Index
  let lines := Fintype.equivFin A
  let triangles := T.projectedTriangle ∘ old.symm
  let equations := equation ∘ lines.symm
  have reindex : (⋃ i, (triangles i).carrier) = ⋃ i, (T.projectedTriangle i).carrier := by
    ext z
    simp only [Set.mem_iUnion, triangles, Function.comp_apply]
    exact ⟨fun ⟨i, h⟩ => ⟨old.symm i, h⟩, fun ⟨i, h⟩ => ⟨old i, by simpa only
      [old.symm_apply_apply] using h⟩⟩
  have full_cover : clipAbove family floor Z = ⋃ i, (triangles i).carrier :=
    T.cover.trans reindex.symm
  let R := constrainedTriangleRefinement triangles equations (fun i => proper (lines.symm i))
    (full_cover ▸ convex_clipAbove family floor Z) (full_cover ▸ inside)
  let : Finite R.Index := R.finite
  let P := commonTriangleRefinement R.triangle
  let parent (i : ULift.{u} P.Index) := old.symm (R.parent i.down.1)
  have contained (i : ULift.{u} P.Index) : (P.triangle i.down).carrier ⊆
      (T.projectedTriangle (parent i)).carrier :=
    (P.triangle_subset i.down).trans (R.subset_parent i.down.1)
  have lift_cover : (⋃ i : P.Index, (P.triangle i).carrier) =
      ⋃ i : ULift.{u} P.Index, (P.triangle i.down).carrier := by
    ext z
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩, fun ⟨i, hi⟩ => ⟨i.down, hi⟩⟩
  let mesh : FloorMesh family floor equation Z :=
    { Index := ULift.{u} P.Index
      finite := inferInstance
      projectedTriangle := fun i => P.triangle i.down
      support i := T.support (parent i)
      cover := full_cover.trans (R.cover.trans (P.total_cover.trans lift_cover))
      separated := fun x y ne => P.separated R.separated (ULift.down_injective.ne ne)
      conforming := fun x y ne z hz => P.conforming R.separated x.down y.down
        (ULift.down_injective.ne ne) z hz
      active i z hz := T.active (parent i) z (contained i hz)
      sign i a := R.signs i.down.1 (lines a)
      alignment i z hz a := by
        have h := R.constrained i.down.1 z (P.triangle_subset i.down hz) (lines a)
        simpa only [equations, Function.comp_apply, lines.symm_apply_apply] using h }
  exact ⟨mesh, parent, contained, fun _ => rfl⟩

namespace LineRefinement

variable {T equation} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance fineIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

/-- Every geometric trace supported on the supplied lines avoids all fine face interiors. -/
theorem interior_avoids_supported_curve (proper : ∀ a, equation a ≠ 0)
    {curve : Set Plane} (support : ∀ p ∈ curve, ∃ a, equation a p = 0) (i : L.mesh.Index) :
    Disjoint (interior ((L.mesh.roof inside).projectedTriangle i).carrier) curve := by
  rw [L.mesh.roof_projectedTriangle inside]
  exact TriangleFamily.interior_avoids_supported_curve L.mesh.projectedTriangle equation proper
    L.mesh.sign L.mesh.alignment support i

theorem roof_normalSlope (i : L.mesh.Index) :
    (L.mesh.roof inside).normalSlope i = (family (T.support (L.parent i))).normalSlope := by
  change (family (L.mesh.support i)).normalSlope = _
  rw [L.same_support]

/-- A connector avoiding the old vertices has at most two incident slopes at
every refined contact, and is transverse whenever they differ. -/
theorem regularSlopes_of_line {a b : Plane} (different : a ≠ b)
    (regular : ∀ (t : ℝ) (i : T.Index) (j : Fin 3),
      AffineMap.lineMap a b t ≠ (T.projectedTriangle i).vertex j)
    (v : L.mesh.pairedComplex.Vertex Set.univ) (t : ℝ)
    (position : AffineMap.lineMap a b t = (L.mesh.roof inside).projectedVertex v) :
    (L.mesh.roof inside).HasRegularSectionSlopes v (b - a) := by
  let plane (i : T.Index) := family (T.support i)
  apply (L.mesh.roof inside).exists_transverse_incidentSlopes_of_regular_line
    T.projectedTriangle T.conforming T.separated (fun i => (plane i).normalSlope)
      (fun i => (plane i).height) L.parent _ (L.roof_normalSlope inside) _ _ v different t position regular
  · intro i
    rw [L.mesh.roof_projectedTriangle inside]
    exact L.contained i
  · intro i x y
    linarith only [(plane i).height_difference y x]
  · intro i j x hi hj
    exact (T.active i x hi).symm.trans (T.active j x hj)

/-- All regular closing-link contacts have zero intrinsic defect, including
their transverse intersections with the projected bank. -/
theorem zeroCurvature_of_regularSlopes (v : L.mesh.pairedComplex.Vertex Set.univ) (d : Plane)
    (regular : (L.mesh.roof inside).HasRegularSectionSlopes v d) :
    L.mesh.pairedComplex.interiorAngularDefect Set.univ v = 0 := by
  let Q := L.mesh.roof inside
  obtain ⟨a, b, slopes, _⟩ := regular
  have contained : Q.incidentSlopes v ⊆ segment ℝ a b := by
    rintro x ⟨f, i, contact, rfl⟩
    rcases slopes f i contact with left | right
    · rw [left]; exact left_mem_segment ℝ _ _
    · rw [right]; exact right_mem_segment ℝ _ _
  exact Q.interiorCurvature_eq_zero_of_normalPolygon_collinear v
    ((collinear_segment a b).subset (convexHull_min contained (convex_segment a b)))

end LineRefinement
end Unfoldings.SpatialEnvelope.FloorMesh
