module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Geometry.FiveSectorInteriors

/-! A nonterminal geometric node on its sector bank must be a leaf. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

/-- A strict original edge fixes the component's chosen sector uniquely. -/
theorem geometricComponentSector_original_parent
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
    (M.geometricComponentSector F covered positive small lower
      (M.geometricComponent F covered (Sum.inl e.val))).sector =
      Sum.inl (K.sourceSectorLabel t origin e.val) := by
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  let data := M.geometricComponentSector F covered positive small lower
    (M.geometricComponent F covered (Sum.inl e.val))
  have closed := data.directions (Sum.inl e.val)
    (M.geometric_original_nonroot F covered positive small lower e.val) rfl
  simp only [geometricParent, dite_eq_right internal, SkirtTailFamily.geometricPosition,
    Sum.elim_inl] at closed
  have strict : K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val ∈
      strictFiveSector t (Sum.inl (K.sourceSectorLabel t origin e.val)) :=
    M.direction e.val e.property
  by_contra different
  exact Set.disjoint_left.mp (strictFiveSector_disjoint_closed positive small
    (fun equal => different equal.symm)) strict closed

/-- Receiving one genuine original parent edge places a node strictly inside its sector. -/
theorem geometric_original_parent_strict_position
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) :
    K.projectedVertex (M.parents.parent e.val) - K.projectedVertex origin ∈
      strictFiveSector t (M.geometricComponentSector F covered positive small lower
        (M.geometricComponent F covered (Sum.inl (M.parents.parent e.val)))).sector := by
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  have positions := mem_closedThreeSector_label_of_backward positive.le small
    (p := K.projectedVertex e.val - K.projectedVertex origin)
    (sub_nonpos.mpr (M.maximal e.val internal))
  have direction := M.direction e.val e.property
  have strict := add_mem_strictThreeSector positions direction
  have vector : (K.projectedVertex e.val - K.projectedVertex origin) +
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) =
        K.projectedVertex (M.parents.parent e.val) - K.projectedVertex origin := by abel
  rw [vector] at strict
  have component := M.geometricComponent_parent F covered (Sum.inl e.val)
  simp only [geometricParent, dite_eq_right internal] at component
  rw [component, M.geometricComponentSector_original_parent F covered positive small lower e]
  exact strict

/-- Sector-bank contacts at actual nonterminal nodes are precisely possible leaf pinches;
an incoming original edge would force strict sector membership. -/
theorem geometric_sector_bank_childless (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
    (bank : F.geometricPosition w - K.projectedVertex origin ∉
      strictFiveSector t (M.geometricComponentSector F covered positive small lower
        (M.geometricComponent F covered w)).sector) :
    ∀ child ∉ (M.geometricParents F covered positive small lower).roots,
      M.geometricParent F covered child ≠ w := by
  intro child child_nonroot same
  cases child with
  | inl z =>
    by_cases boundary : C.IsBoundaryVertex Set.univ z
    · simp only [geometricParent, dite_eq_left boundary] at same
      exact nonroot ⟨F.rimComponent covered z boundary, same⟩
    · have old_nonroot : z ∉ M.parents.roots := by
        simpa only [M.roots_eq, Set.mem_ofPred_eq] using boundary
      simp only [geometricParent, dite_eq_right boundary] at same
      apply bank
      rw [← same]
      exact M.geometric_original_parent_strict_position F covered positive small lower
        ⟨z, old_nonroot⟩
  | inr child =>
    cases child with
    | inl c => exact nonroot ⟨c.val, same⟩
    | inr c => exact child_nonroot ⟨c, rfl⟩

end Unfoldings.ConvexCap.SectorForest
