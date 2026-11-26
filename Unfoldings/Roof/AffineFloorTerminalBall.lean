module

public import Unfoldings.Roof.AffineFloorChartSkeleton
public import Unfoldings.Geometry.ConformingPointMultiplicity
public import Unfoldings.Roof.CurvatureNormalInterior

/-! A small ball about a trimmed endpoint meets only its original incident triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open Topology

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)

/-- Control the terminal neighborhood simultaneously for every coarse face and corner. -/
theorem exists_terminalBall_of_off_corners {p : Plane}
    (h : ∀ i : T.Index × Fin 3, p ≠ (T.projectedTriangle i.1).vertex i.2) :
    ∃ r : ℝ, 0 < r ∧
      (∀ q ∈ Metric.ball p r, ∀ i : T.Index × Fin 3, q ≠ (T.projectedTriangle i.1).vertex i.2) ∧
      ∀ q ∈ Metric.ball p r, ∀ f : T.Index, q ∈ (T.projectedTriangle f).carrier →
        p ∈ (T.projectedTriangle f).carrier := by
  classical
  letI : Finite T.Index := T.finite
  have off : ∀ᶠ q in 𝓝 p, ∀ i : T.Index × Fin 3, q ≠ (T.projectedTriangle i.1).vertex i.2 := by
    apply Filter.eventually_all.mpr
    intro i
    exact isClosed_singleton.isOpen_compl.mem_nhds (h i)
  have in_star : ∀ᶠ q in 𝓝 p, ∀ f : T.Index,
      q ∈ (T.projectedTriangle f).carrier → p ∈ (T.projectedTriangle f).carrier := by
    apply Filter.eventually_all.mpr
    intro f
    by_cases member : p ∈ (T.projectedTriangle f).carrier
    · exact Filter.Eventually.of_forall (fun _ _ => member)
    · have off : ∀ᶠ q in 𝓝 p, q ∉ (T.projectedTriangle f).carrier :=
        (T.projectedTriangle f).compact_carrier.isClosed.isOpen_compl.mem_nhds member
      exact off.mono (fun _ exclude hit => (exclude hit).elim)
  obtain ⟨r, pos, control⟩ := Metric.eventually_nhds_iff_ball.mp (off.and in_star)
  exact ⟨r, pos, fun q hq => (control q hq).1, fun q hq => (control q hq).2⟩

namespace LineRefinement

variable {T} {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance terminalIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

/-- No new curved vertex can occur away from an original corner, for any upward graph chart. -/
theorem zeroCurvature_of_off_chartCorners (E : Plane ≃ₗᵢ[ℝ] Plane)
    (w : L.mesh.pairedComplex.Vertex Set.univ)
    (off : ∀ i : T.Index × Fin 3, ((L.mesh.roof inside).reorient E).projectedVertex w ≠ T.chartCorner E i) :
    L.mesh.pairedComplex.interiorAngularDefect Set.univ w = 0 := by
  let R := L.mesh.roof inside
  let Q := R.reorient E
  have away (i : T.Index) : ¬ (T.projectedTriangle i).IsVertex (R.projectedVertex w) := by
    rintro ⟨j, eq⟩
    apply off (i, j)
    rw [ConvexRoof.projectedVertex_reorient]
    exact congrArg E eq.symm
  have contains (f : L.mesh.Index) (i : Fin 3)
      (at_w : L.mesh.pairedComplex.vertexOfCorner Set.univ (f, i) = w) :
      R.projectedVertex w ∈ (T.projectedTriangle (L.parent f)).carrier := by
    have at_corner : R.projectedVertex w = (R.projectedTriangle f).vertex i :=
      (congrArg R.projectedVertex at_w).symm.trans (R.projectedVertex_ofCorner f i)
    rw [at_corner]
    apply L.contained f
    rw [← L.mesh.roof_projectedTriangle inside]
    exact (R.projectedTriangle f).vertex_mem i
  obtain ⟨⟨f₀, i₀⟩, at_w₀⟩ := L.mesh.pairedComplex.vertexOfCorner_surjective Set.univ w
  obtain ⟨j, only_two⟩ := TriangleFamily.atMostTwo_faces_of_nonvertex T.projectedTriangle
    T.conforming T.separated (L.parent f₀) (contains f₀ i₀ at_w₀) (away _)
  let a := (family (T.support (L.parent f₀))).normalSlope
  let b := (family (T.support j)).normalSlope
  have included : R.incidentSlopes w ⊆ segment ℝ a b := by
    rintro x ⟨f, i, at_w, rfl⟩
    change R.normalSlope f ∈ segment ℝ a b
    rw [L.roof_normalSlope inside]
    rcases only_two (L.parent f) (contains f i at_w) with h | h
    · rw [h]
      exact left_mem_segment ℝ _ _
    · rw [h]
      exact right_mem_segment ℝ _ _
  exact R.interiorCurvature_eq_zero_of_normalPolygon_collinear w
    ((collinear_segment a b).subset (convexHull_min included (convex_segment a b)))

end LineRefinement
end Unfoldings.SpatialEnvelope.FloorMesh
