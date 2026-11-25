module

public import Unfoldings.Roof.AffineFloorClosingMesh
public import Unfoldings.Roof.HorizontalReorientation

/-! Refine in any horizontal chart while keeping the actual original roof and its supports. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E : Plane ≃ₗᵢ[ℝ] Plane) {n : ℕ} (P : PolygonalChain Plane n) (c : Plane)

/-- Mark the two trimmed endpoints and the auxiliary bend in the chosen chart. -/
def closingMark (i : Fin 3) : Plane :=
  ![P.vertex 0, P.vertex (Fin.last n), c] i

abbrev ChartClosingLine (n : ℕ) :=
  ULift.{u} (((Fin n ⊕ Fin 4) ⊕ Bool) ⊕ (Fin 3 × Fin 2))

/-- The same proper supporting lines are pulled back to the physical mesh. -/
def chartClosingEquations (i : ChartClosingLine.{u} n) : Plane →ᵃ[ℝ] ℝ :=
  (i.down.elim (fun j => closingEquations.{u} P c (ULift.up j))
    (fun k => pointCoordinateEquation (closingMark P c k.1) k.2)).comp
      E.toLinearEquiv.toAffineEquiv.toAffineMap

theorem chartClosingEquations_ne_zero (i : ChartClosingLine.{u} n) :
    chartClosingEquations E P c i ≠ 0 := by
  let line := i.down.elim (fun j => closingEquations.{u} P c (ULift.up j))
    (fun k => pointCoordinateEquation (closingMark P c k.1) k.2)
  have proper : line ≠ 0 := by
    rcases i with ⟨j | k⟩
    · exact closingEquations_ne_zero.{u} P c (ULift.up j)
    · exact pointCoordinateEquation_ne_zero _ _
  intro zero
  apply proper
  ext p
  have h := DFunLike.congr_fun zero (E.symm p)
  change line (E (E.symm p)) = 0 at h
  rw [E.apply_symm_apply] at h
  exact h

/-- Refine the same physical envelope along the chart's bank and connector. -/
def chartClosingMesh (inside : (interior (clipAbove family floor Z)).Nonempty) :
    T.LineRefinement (chartClosingEquations E P c) :=
  T.refineToLines (chartClosingEquations E P c) (chartClosingEquations_ne_zero E P c) inside

variable (inside : (interior (clipAbove family floor Z)).Nonempty)

local notation "L" => chartClosingMesh T E P c inside
local instance chartClosingFintype : Fintype (L).mesh.Index := @Fintype.ofFinite _ (L).mesh.finite

/-- The new intrinsic triangulation is read in the chosen planar chart. -/
def chartClosingRoof : ConvexRoof (L).mesh.pairedComplex :=
  ((L).mesh.roof inside).reorient E

local notation "Q" => chartClosingRoof T E P c inside

theorem chartClosingRoof_triangle_carrier (f : (L).mesh.Index) :
    ((Q).projectedTriangle f).carrier = E '' ((L).mesh.projectedTriangle f).carrier := by
  rw [chartClosingRoof, ConvexRoof.projectedTriangle_reorient_carrier, (L).mesh.roof_projectedTriangle]

/-- Supported traces in the new chart avoid the interiors of all refined triangles. -/
theorem chartClosingRoof_disjoint_supported {S : Set Plane}
    (supports : ∀ p ∈ S, ∃ i : ChartClosingLine.{u} n, chartClosingEquations E P c i (E.symm p) = 0)
    (f : (L).mesh.Index) : Disjoint (interior ((Q).projectedTriangle f).carrier) S := by
  rw [chartClosingRoof_triangle_carrier]
  change Disjoint (interior (E.toHomeomorph '' ((L).mesh.projectedTriangle f).carrier)) S
  rw [← E.toHomeomorph.image_interior]
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, interior, rfl⟩ on_trace
  obtain ⟨i, h⟩ := supports (E p) on_trace
  rw [E.symm_apply_apply] at h
  have forbidden := (L).interior_avoids_supported_curve inside
    (chartClosingEquations_ne_zero E P c)
    (curve := {q | chartClosingEquations E P c i q = 0}) (fun _ hit => ⟨i, hit⟩) f
  rw [(L).mesh.roof_projectedTriangle inside] at forbidden
  exact Set.disjoint_left.mp forbidden interior h

/-- The actual path and both connector links lie in the refined skeleton. -/
theorem chartClosingRoof_disjoint_paths (f : (L).mesh.Index) :
    Disjoint (interior ((Q).projectedTriangle f).carrier)
      (Set.range P.path ∪ Set.range (P.forwardClosingChain c).path) := by
  apply chartClosingRoof_disjoint_supported T E P c inside _ f
  intro p member
  have closure : p ∈ P.threeSegmentClosure (P.vertex 0) c := by
    rw [P.threeSegmentClosure_of_initial_eq_twoLinkClosure c]
    rcases member with bank | closing
    · exact Or.inl bank
    · rw [P.forwardClosingChain_trace c] at closing
      exact Or.inr closing
  obtain ⟨i, supported⟩ := P.closureEquations_support (P.vertex 0) c p closure
  refine ⟨⟨.inl (.inl i)⟩, ?_⟩
  change P.closureEquations (P.vertex 0) c i (E (E.symm p)) = 0
  rwa [E.apply_symm_apply]

/-- The fine triangles do not straddle either vertical end line. -/
theorem chartClosingRoof_interior_avoids_endLines (f : (L).mesh.Index) {p : Plane}
    (interior_face : p ∈ interior ((Q).projectedTriangle f).carrier) :
    p 0 ≠ P.vertex 0 0 ∧ p 0 ≠ P.vertex (Fin.last n) 0 := by
  have off (b : Bool) : Disjoint (interior ((Q).projectedTriangle f).carrier)
      {q : Plane | pointCoordinateEquation (if b then P.vertex (Fin.last n) else P.vertex 0) 0 q = 0} := by
    apply chartClosingRoof_disjoint_supported T E P c inside _ f
    intro q hit
    refine ⟨⟨.inl (.inr b)⟩, ?_⟩
    change pointCoordinateEquation (if b then P.vertex (Fin.last n) else P.vertex 0) 0
      (E (E.symm q)) = 0
    rwa [E.apply_symm_apply]
  exact ⟨fun eq => Set.disjoint_left.mp (off false) interior_face (sub_eq_zero.mpr eq),
    fun eq => Set.disjoint_left.mp (off true) interior_face (sub_eq_zero.mpr eq)⟩

theorem chartClosingRoof_footprint :
    (Q).footprint = E '' clipAbove family floor Z := by
  rw [chartClosingRoof, ConvexRoof.footprint_reorient, (L).mesh.roof_footprint]

/-- The three marked corner points are actual intrinsic vertices of the
refined chart, even if one of the two links is collinear with the other. -/
theorem exists_chartClosingRoof_markedVertex (i : Fin 3)
    (in_roof : closingMark P c i ∈ (Q).footprint) :
    ∃ v : (L).mesh.pairedComplex.Vertex Set.univ, (Q).projectedVertex v = closingMark P c i := by
  let p := closingMark P c i
  have in_domain : E.symm p ∈ clipAbove family floor Z := by
    rw [chartClosingRoof_footprint] at in_roof
    obtain ⟨q, hq, equal⟩ := in_roof
    change E q = p at equal
    rw [← equal, E.symm_apply_apply]
    exact hq
  obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp ((L).mesh.cover.subset in_domain)
  have on_chart : p ∈ ((Q).projectedTriangle f).carrier := by
    rw [chartClosingRoof_triangle_carrier]
    exact ⟨E.symm p, on_face, E.apply_symm_apply p⟩
  let mark (k : Fin 2) : ChartClosingLine.{u} n := ⟨.inr (i, k)⟩
  have signs (k : Fin 2) (z : Plane) (hz : z ∈ ((Q).projectedTriangle f).carrier) :
      0 ≤ AffineArrangement.signed (pointCoordinateEquation p k) ((L).mesh.sign f (mark k)) z := by
    rw [chartClosingRoof_triangle_carrier] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have h := (L).mesh.alignment f x hx (mark k)
    have value : chartClosingEquations E P c (mark k) x = pointCoordinateEquation p k (E x) := rfl
    rw [AffineArrangement.signed_apply] at h ⊢
    rwa [value] at h
  obtain ⟨j, vertex⟩ := ((Q).projectedTriangle f).isVertex_of_coordinate_signs p
    (fun k => (L).mesh.sign f (mark k)) signs on_chart
  exact ⟨(L).mesh.pairedComplex.vertexOfCorner Set.univ (f, j),
    ((Q).projectedVertex_ofCorner f j).trans vertex⟩

end Unfoldings.SpatialEnvelope.FloorMesh
