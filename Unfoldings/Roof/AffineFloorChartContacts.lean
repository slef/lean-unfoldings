module

public import Unfoldings.Roof.AffineFloorLineRefinement
public import Unfoldings.Roof.HorizontalReorientation
public import Unfoldings.Roof.RefinedCornerSlopes

/-! Regular contacts and trimmed corners on the same physical roof in a bank chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {T : FloorMesh family floor extra Z}
  {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)
  (E : Plane ≃ₗᵢ[ℝ] Plane)

local instance originalIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance chartingIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

local notation "K" => T.roof inside
local notation "R" => L.mesh.roof inside
local notation "Q" => ConvexRoof.reorient (L.mesh.roof inside) E
local notation "faceAt" => fun (i : T.Index) (j : Fin 3) => E (Triangle.vertex (T.projectedTriangle i) j)

theorem chart_normalSlope (f : L.mesh.Index) :
    (Q).normalSlope f = ((K).reorient E).normalSlope (L.parent f) := by
  rw [ConvexRoof.normalSlope_reorient, ConvexRoof.normalSlope_reorient, L.roof_normalSlope]
  rfl

/-- Each fine face measures a lifted chart direction in its original support plane. -/
theorem chart_sectionDirection (f : L.mesh.Index) (d : Plane) :
    (Q).sectionDirection f d = ((K).reorient E).sectionDirection (L.parent f) d := by
  simp only [ConvexRoof.sectionDirection, L.chart_normalSlope inside E]

/-- A chart line avoiding every original corner has regular contacts on its physical refinement. -/
theorem regularSlopes_of_chart_line {a b : Plane} (different : a ≠ b)
    (regular : ∀ (t : ℝ) (i : T.Index) (j : Fin 3), AffineMap.lineMap a b t ≠ (faceAt) i j)
    (w : L.mesh.pairedComplex.Vertex Set.univ) (t : ℝ)
    (position : AffineMap.lineMap a b t = (Q).projectedVertex w) :
    (Q).HasRegularSectionSlopes w (b - a) := by
  let U := E.toLinearEquiv.toAffineEquiv.toAffineMap
  have mapped (s : ℝ) : E (AffineMap.lineMap (E.symm a) (E.symm b) s) =
      AffineMap.lineMap a b s := by
    change U (AffineMap.lineMap (E.symm a) (E.symm b) s) = _
    rw [U.apply_lineMap]
    change AffineMap.lineMap (E (E.symm a)) (E (E.symm b)) s = _
    rw [E.apply_symm_apply, E.apply_symm_apply]
  have actual : AffineMap.lineMap (E.symm a) (E.symm b) t = (R).projectedVertex w := by
    apply E.injective
    rwa [mapped, ← (R).projectedVertex_reorient E w]
  obtain ⟨p, q, slopes, transverse⟩ := L.regularSlopes_of_line inside
    (E.symm.injective.ne different) (fun s i j eq =>
      regular s i j ((mapped s).symm.trans (congrArg E eq))) w t actual
  refine ⟨E p, E q, fun f i contact => ?_, ?_⟩
  · rw [(R).normalSlope_reorient E]
    exact (slopes f i contact).imp (congrArg E) (congrArg E)
  · refine transverse.imp (congrArg E) ?_
    intro unequal
    have displacement : b - a = E (E.symm b - E.symm a) := by
      rw [map_sub, E.apply_symm_apply, E.apply_symm_apply]
    rwa [displacement, ← map_sub, E.inner_map_map]

/-- Along an old open edge, the refined support slopes are tied along the actual chart edge. -/
theorem exists_tangentSlopes_of_chart_edge (w : L.mesh.pairedComplex.Vertex Set.univ)
    (i : T.Index) (j : Fin 3)
    (edge : (Q).projectedVertex w ∈ segment ℝ ((faceAt) i j) ((faceAt) i (Triangle.next j)))
    (regular : ∀ k, (Q).projectedVertex w ≠ (faceAt) i k) :
    ∃ a b : Plane,
      (∀ f k, L.mesh.pairedComplex.vertexOfCorner Set.univ (f, k) = w →
        (Q).normalSlope f = a ∨ (Q).normalSlope f = b) ∧
      inner ℝ (a - b) ((faceAt) i (Triangle.next j) - (faceAt) i j) = 0 := by
  let plane (k : T.Index) := family (T.support k)
  have physical : (R).projectedVertex w ∈ (T.projectedTriangle i).edge j := by
    rw [(R).projectedVertex_reorient] at edge
    let U := E.toLinearEquiv.toAffineEquiv.toAffineMap
    change U ((R).projectedVertex w) ∈
      segment ℝ (U ((T.projectedTriangle i).vertex j))
        (U ((T.projectedTriangle i).vertex (Triangle.next j))) at edge
    rw [← image_segment ℝ U] at edge
    obtain ⟨v, on_edge, eq⟩ := edge
    exact E.injective eq ▸ on_edge
  have not_corner : ¬ (T.projectedTriangle i).IsVertex ((R).projectedVertex w) := by
    rintro ⟨k, eq⟩
    apply regular k
    rw [(R).projectedVertex_reorient, ← eq]
  obtain ⟨a, b, slopes, tangent⟩ := (R).exists_tangent_incidentSlopes_on_old_edge
    T.projectedTriangle T.conforming T.separated (fun k => (plane k).normalSlope)
    (fun k => (plane k).height) L.parent (fun f => by rw [L.mesh.roof_projectedTriangle]; exact L.contained f)
    (L.roof_normalSlope inside) (fun k x y => by linarith only [(plane k).height_difference y x])
    (fun i j x hi hj => (T.active i x hi).symm.trans (T.active j x hj)) w i j physical not_corner
  refine ⟨E a, E b, fun f k contact => ?_, ?_⟩
  · rw [(R).normalSlope_reorient E]
    exact (slopes f k contact).imp (congrArg E) (congrArg E)
  · change inner ℝ (E a - E b) (E _ - E _) = 0
    rwa [← map_sub, ← map_sub, E.inner_map_map]

/-- Within one original face all incident fine supports are exactly its support. -/
theorem chart_slope_eq_of_mem_original_interior (w : L.mesh.pairedComplex.Vertex Set.univ)
    (i : T.Index) (interior_mem : (R).projectedVertex w ∈ interior (T.projectedTriangle i).carrier)
    (f : L.mesh.Index) (j : Fin 3) (contact : L.mesh.pairedComplex.vertexOfCorner Set.univ (f, j) = w) :
    (Q).normalSlope f = ((K).reorient E).normalSlope i := by
  rw [(R).normalSlope_reorient, (K).normalSlope_reorient]
  apply congrArg E
  exact (R).refined_slope_eq_of_mem_old_interior T.projectedTriangle T.conforming
    (fun g => (family (T.support g)).normalSlope) L.parent
    (fun g => by rw [L.mesh.roof_projectedTriangle]; exact L.contained g)
    (L.roof_normalSlope inside) w i interior_mem f j contact

end Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement
