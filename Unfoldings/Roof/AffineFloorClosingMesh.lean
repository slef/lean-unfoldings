module

public import Unfoldings.Roof.AffineFloorLineRefinement
public import Unfoldings.Geometry.TwoLinkMonotoneChain
public import Unfoldings.Geometry.TwoLinkClosureAlignment
public import Unfoldings.Geometry.MarkedPointConstraints

/-! The actual bank, near-chord closing links, and end lines share one physical roof refinement. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  {n : ℕ} (P : PolygonalChain Plane n) (c : Plane)

/-- The path supports, connector supports and two vertical end lines. -/
def closingEquations : ULift.{u} ((Fin n ⊕ Fin 4) ⊕ Bool) → Plane →ᵃ[ℝ] ℝ :=
  fun i => Sum.elim (P.closureEquations (P.vertex 0) c)
    (fun b => pointCoordinateEquation (if b then P.vertex (Fin.last n) else P.vertex 0) 0) i.down

theorem closingEquations_ne_zero (i : ULift.{u} ((Fin n ⊕ Fin 4) ⊕ Bool)) :
    closingEquations P c i ≠ 0 := by
  rcases i with ⟨i | i⟩
  · exact P.closureEquations_ne_zero (P.vertex 0) c i
  · exact pointCoordinateEquation_ne_zero _ _

/-- Align the affine-floor mesh to the bank and closing links and both vertical end lines. -/
def closingMesh (inside : (interior (clipAbove family floor Z)).Nonempty) :
    T.LineRefinement (closingEquations P c) :=
  T.refineToLines (closingEquations P c) (closingEquations_ne_zero P c) inside

variable (inside : (interior (clipAbove family floor Z)).Nonempty)

local notation "L" => closingMesh T P c inside
local instance closingMeshFintype : Fintype (L).mesh.Index := @Fintype.ofFinite _ (L).mesh.finite

/-- The entire projected bank and both actual closing links run on the refined edges. -/
theorem closingMesh_interior_disjoint_paths (f : (L).mesh.Index) :
    Disjoint (interior (((L).mesh.roof inside).projectedTriangle f).carrier)
      (Set.range P.path ∪ Set.range (P.forwardClosingChain c).path) := by
  apply (L).interior_avoids_supported_curve inside (closingEquations_ne_zero P c) _ f
  intro z member
  have closure : z ∈ P.threeSegmentClosure (P.vertex 0) c := by
    rw [P.threeSegmentClosure_of_initial_eq_twoLinkClosure c]
    rcases member with bank | closing
    · exact Or.inl bank
    · rw [P.forwardClosingChain_trace c] at closing
      exact Or.inr closing
  obtain ⟨i, supported⟩ := P.closureEquations_support (P.vertex 0) c z closure
  exact ⟨⟨.inl i⟩, supported⟩

/-- Both vertical end lines avoid every fine face interior. -/
theorem closingMesh_interior_avoids_endLines (f : (L).mesh.Index) (z : Plane)
    (interior_face : z ∈ interior (((L).mesh.roof inside).projectedTriangle f).carrier) :
    z 0 ≠ P.vertex 0 0 ∧ z 0 ≠ P.vertex (Fin.last n) 0 := by
  have avoids (b : Bool) :
      Disjoint (interior (((L).mesh.roof inside).projectedTriangle f).carrier)
        {q : Plane | pointCoordinateEquation (if b then P.vertex (Fin.last n) else P.vertex 0) 0 q = 0} :=
    (L).interior_avoids_supported_curve inside (closingEquations_ne_zero P c)
      (fun _ h => ⟨⟨.inr b⟩, h⟩) f
  constructor
  · intro equal
    exact Set.disjoint_left.mp (avoids false) interior_face (sub_eq_zero.mpr equal)
  · intro equal
    exact Set.disjoint_left.mp (avoids true) interior_face (sub_eq_zero.mpr equal)

end Unfoldings.SpatialEnvelope.FloorMesh
