module

public import Unfoldings.Roof.SkirtAttachments
public import Unfoldings.Roof.ExtendedCutLabels

/-! The complete geometric original-cut and skirt network is an explicit finite parent forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SkirtTailFamily

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {outer : Set Plane} {q : Plane} (F : K.SkirtTailFamily outer q)

/-- Nonconstant skirt components without an original rim attachment need their own leaf. -/
def IndependentComponent := {c : F.Component //
  F.componentSeed c ≠ (F.componentTail c).tip ∧
    ¬ ∃ w : C.Vertex Set.univ,
      C.IsBoundaryVertex Set.univ w ∧ K.projectedVertex w = F.componentSeed c}

abbrev GeometricVertex := C.Vertex Set.univ ⊕ (F.IndependentComponent ⊕ F.Component)

instance geometricVertexFinite : Finite F.GeometricVertex := by
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  unfold GeometricVertex IndependentComponent
  infer_instance

def geometricPosition : F.GeometricVertex → Plane :=
  Sum.elim K.projectedVertex
    (Sum.elim (fun c => F.componentSeed c.val) (fun c => (F.componentTail c).tip))

theorem component_source_distance_lt (c : F.Component)
    (genuine : F.componentSeed c ≠ (F.componentTail c).tip) :
    dist q (F.componentSeed c) < dist q (F.componentTail c).tip := by
  have strict := dist_lineMap_lt_of_inner_nonneg q (F.componentSeed c) (F.componentTail c).tip
    (F.componentTail c).radial_outward genuine (t := 0) (s := 1) le_rfl zero_lt_one
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using strict

theorem rim_vertex_ne_tip (c : F.Component) (w : C.Vertex Set.univ) :
    K.projectedVertex w ≠ (F.componentTail c).tip := by
  intro same
  have inside := F.encloses (K.projectedVertex_mem_footprint w)
  exact (F.componentTail c).boundary.2 (same ▸ inside)

end Unfoldings.ConvexRoof.SkirtTailFamily

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

open scoped Classical in
def geometricParent : F.GeometricVertex → F.GeometricVertex
  | Sum.inl w => if boundary : C.IsBoundaryVertex Set.univ w then
      Sum.inr (Sum.inr (F.rimComponent covered w boundary)) else Sum.inl (M.parents.parent w)
  | Sum.inr (Sum.inl c) => Sum.inr (Sum.inr c.val)
  | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)

/-- Original trees continue to their unique skirt tips; independent radial segments supply
additional leaves. All genuine edges strictly increase source distance. -/
def geometricParents (positive : 0 < t) (small : t < 1) :
    AscendingParents F.GeometricVertex where
  roots := Set.range (fun c : F.Component => Sum.inr (Sum.inr c))
  parent := M.geometricParent F covered
  height w := dist (origin) (F.geometricPosition w)
  fixed_root := by
    rintro _ ⟨c, rfl⟩
    rfl
  ascending := by
    intro w nonroot
    cases w with
    | inl w =>
      by_cases boundary : C.IsBoundaryVertex Set.univ w
      · let c := F.rimComponent covered w boundary
        have seed : K.projectedVertex w = F.componentSeed c :=
          F.rim_vertex_eq_seed c w boundary (F.rimComponent_mem covered w boundary)
        have genuine : F.componentSeed c ≠ (F.componentTail c).tip := by
          intro equal
          exact F.rim_vertex_ne_tip c w (seed.trans equal)
        simp only [geometricParent, dite_eq_left boundary, SkirtTailFamily.geometricPosition,
          Sum.elim_inl, Sum.elim_inr]
        rw [seed]
        exact F.component_source_distance_lt c genuine
      · have original_nonroot : w ∉ M.parents.roots := by
          simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
        simp only [geometricParent, dite_eq_right boundary, SkirtTailFamily.geometricPosition,
          Sum.elim_inl]
        exact M.parent_source_distance_lt positive small ⟨w, original_nonroot⟩
    | inr w =>
      cases w with
      | inl c => exact F.component_source_distance_lt c.val c.property.1
      | inr c => exact (nonroot ⟨c, rfl⟩).elim

theorem geometricParents_original_parent (positive : 0 < t) (small : t < 1)
    (w : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ w) :
    (M.geometricParents F covered positive small).parent (Sum.inl w) =
      Sum.inl (M.parents.parent w) := dite_eq_right internal

theorem geometricParents_rim_parent (positive : 0 < t) (small : t < 1)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) :
    (M.geometricParents F covered positive small).parent (Sum.inl w) =
      Sum.inr (Sum.inr (F.rimComponent covered w boundary)) := dite_eq_left boundary

end Unfoldings.ConvexRoof.SectorForest
