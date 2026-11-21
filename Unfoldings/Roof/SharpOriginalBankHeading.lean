module

public import Unfoldings.Roof.CompletionRegularHalfTurn
public import Unfoldings.Roof.CompletionOriginalBankWindowTrace
public import Unfoldings.Roof.CompletionProjectedBankWindow
public import Unfoldings.Roof.ProjectedBankDirections
public import Unfoldings.Geometry.CompactHalfTurnClosure
public import Unfoldings.Cap.SharpOriginalRadialTurns

/-! The sharp heading budget for actual original banks on a strict half-turn window. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real InnerProductGeometry

universe u v

local instance sharpBankIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {I : Type u} {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

namespace CompletionMesh

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane} {I : Type u}
  {extra : I → Plane →ᵃ[ℝ] ℝ}

/-- Use the same completion mesh with a smaller prescribed region. -/
def restrictRegion (E : K.CompletionMesh φ region extra) {U : Set Plane} (contained : U ⊆ region) :
    K.CompletionMesh φ U extra where
  tentHeight := E.tentHeight
  level := E.level
  mesh := E.mesh
  conforming := E.conforming
  covers := (Set.union_subset_union (Set.Subset.refl _) contained).trans E.covers
  unchanged := E.unchanged

end CompletionMesh

/-- The geometric budget depends on the curve, bank trace and endpoint locations. -/
private theorem transfer_geometric_bank_bound {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} (D : ConvexCap C)
    {J J' bank bank' : Set Plane} {a a' b b' q c : Plane}
    (curve : J' = J) (trace : bank' = bank) (first : a' = a) (last : b' = b)
    (jordan : Schoenflies.IsJordanCurve J) (jordan' : Schoenflies.IsJordanCurve J')
    (inside : J ⊆ D.footprint) (inside' : J' ⊆ D.footprint)
    (avoid : ∀ f, Disjoint (interior (D.projectedTriangle f).carrier) J)
    (avoid' : ∀ f, Disjoint (interior (D.projectedTriangle f).carrier) J') {budget : ℝ}
    (bound : |∑ i ∈ D.jordanGeometricBankIndices jordan inside avoid bank
        (radialClosingCorners q a b c), D.jordanContourTurnError jordan inside avoid i| ≤ budget) :
    |∑ i ∈ D.jordanGeometricBankIndices jordan' inside' avoid' bank'
        (radialClosingCorners q a' b' c), D.jordanContourTurnError jordan' inside' avoid' i| ≤
      budget := by
  subst J' bank' a' b'
  exact bound

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

open Classical in
/-- At the actual tilt, the difference of the untrimmed spatial bank heading and its
projected heading is at most the sharp allowance. The auxiliary closure can avoid all
old vertices because its compact region is chosen before the first triangulation. -/
theorem abs_projectedMetricHeadingError_le_sharp_of_halfturn
    {φ : ℝ} (positive : 0 < φ) (small_tilt : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    {retain : Set C.Seam} {n : ℕ} (coarse : (C.boundarySystem retain).Chain (n + 1))
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val))
    (source : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom source 0)
    {γ : ℝ} (margin_pos : 0 < γ)
    (margin : let P := K.folding.projectedBoundaryChain coarse
      ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (window : let P := K.folding.projectedBoundaryChain coarse
      (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
        (P.internalSourceRay source k.succ)) < π) :
    |K.projectedMetricHeadingError coarse (Fin.last (n + 1))| ≤ shallowDevelopmentHeading φ := by
  let P := K.folding.projectedBoundaryChain coarse
  have genuine (i : Fin (n + 2)) : P.edge i ≠ 0 :=
    K.projectedBoundaryChain_edge_ne_zero coarse i
  obtain ⟨region, compact, convex, _, choose⟩ :=
    P.exists_compact_regular_halfturn_closure source radial genuine margin_pos margin window
  let eq : ULift.{u} (Fin (n + 2) ⊕ Fin 4) → Plane →ᵃ[ℝ] ℝ :=
    fun i => P.closureEquations source source i.down
  have eq_proper (i) : eq i ≠ 0 := P.closureEquations_ne_zero source source i.down
  obtain ⟨E₀⟩ := K.exists_completionMesh positive small_tilt compact eq eq_proper
  let point (i : E₀.mesh.Index × Fin 3) := (E₀.mesh.projectedTriangle i.1).vertex i.2
  let : Finite E₀.mesh.Index := E₀.mesh.finite
  obtain ⟨a, b, first, last, q, c, height, _, radial', initial, progress, supported, outside,
    outward, regular, trim_avoids, links_regular, jordan, contained⟩ :=
    choose point E₀.oldEdgeEquation E₀.oldEdgeEquation_ne_zero zero_lt_one
  let Q := P.trimEnds a b
  have trimmed_genuine (i : Fin (n + 2)) : Q.edge i ≠ 0 := by
    rw [P.trimEnds_edge]
    apply smul_ne_zero _ (genuine i)
    split_ifs <;> linarith [first.2, last.1]
  have bank_avoids (f : E₀.mesh.Index) :
      Disjoint (interior (E₀.mesh.projectedTriangle f).carrier) (Set.range Q.path) := by
    apply E₀.mesh.interior_avoids_supported_curve eq_proper _ f
    intro p member
    obtain ⟨i, equal⟩ := P.closureEquations_support source source p
      (Or.inl (P.trimEnds_path_subset a b member))
    exact ⟨ULift.up i, equal⟩
  obtain ⟨inside, avoids, budget⟩ := E₀.sharp_radial_bank_bound_of_regular_closure
    Q q c radial' trimmed_genuine initial progress height supported outside outward jordan contained
    bank_avoids (fun f k => trim_avoids (f, k)) (fun i => (regular i).2)
    (fun j t f k => links_regular j t (f, k)) positive small_tilt height_bound tilt
  let eq' := K.combinedCompletionEquations (Q.markedClosureEquations q c)
  let L := E₀.alignToLines eq' (K.combinedCompletionEquations_ne_zero _
    (Q.markedClosureEquations_ne_zero q c))
  have filling : PlanarTopology.closedJordanDomain (Q.threeSegmentClosure q c) ⊆ region :=
    PlanarTopology.closedJordanDomain_subset_convex jordan compact convex contained
  let E := L.restrictRegion filling
  let V := E.originalConstraintView
  let W := CompletionMesh.markedOriginalBankWindow coarse cut a b q c first.2 last.2 jordan E
  have trace := W.cap_projected_trace_eq_trim source radial
  have closure := W.cap_projected_closure_eq_trim source radial q c
  have start := W.cap_projected_initial.trans (P.trimEnds_start a b).symm
  have finish := W.cap_projected_terminal.trans (P.trimEnds_last a b).symm
  let P' := V.cap.projectedBoundaryChain V.originalPieceSet W.chain
  have supported' : ∀ p ∈ Set.range P'.path, 0 ≤ height (p - q) :=
    fun p hp => supported p (trace.subset hp)
  have initial' : 0 < dist q (P'.vertex 0) := by rwa [start]
  have outward' : 0 < inner ℝ (P'.vertex (Fin.last (W.length + 1)) - q)
      (c - P'.vertex (Fin.last (W.length + 1))) := by rwa [finish]
  have jordan' : Schoenflies.IsJordanCurve (P'.threeSegmentClosure q c) := by
    rw [closure]
    exact jordan
  have inside' : P'.threeSegmentClosure q c ⊆ interior V.cap.footprint :=
    closure.subset.trans inside
  have avoids' (f : V.mesh.Index) : Disjoint (interior (V.cap.projectedTriangle f).carrier)
      (P'.threeSegmentClosure q c) := (avoids f).mono_right closure.subset
  have bound' : |∑ i ∈ V.cap.jordanGeometricBankIndices jordan'
      (inside'.trans interior_subset) avoids' (Set.range P'.path)
        (radialClosingCorners q (P'.vertex 0) (P'.vertex (Fin.last (W.length + 1))) c),
      V.cap.jordanContourTurnError jordan' (inside'.trans interior_subset) avoids' i| ≤
    shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ :=
    transfer_geometric_bank_bound V.cap closure trace start finish jordan jordan'
      (inside.trans interior_subset) (inside'.trans interior_subset) avoids avoids' budget
  let roll := V.cap.boundaryChainRollHeading_sub_projectedFanRollHeading_last
    V.originalPieceSet W.chain
  have estimate := V.cap.abs_sum_original_radial_chain_turnError_le_sharp
    V.originalPieceSet W.chain q c (W.cap_projected_radialFrom_trim source radial q radial')
    initial' height supported' outside outward' jordan' inside' avoids' positive.le small_tilt
    (V.cap_tilt positive small_tilt tilt) bound'
  exact (congrArg abs ((W.terminal_real_error_eq last.1).symm.trans roll)).le.trans estimate

end Unfoldings.ConvexRoof
