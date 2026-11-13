module

public import Unfoldings.Roof.ExtendedComponentWedges
public import Unfoldings.Geometry.FiveSectors

/-! Every actual geometric cut component lies in one of the five fixed sectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

/-- The two additional forward sectors are needed only for independent skirt components. -/
theorem exists_cut_component_sector (positive : 0 < t) (small : t < 1) (c : F.Component) :
    ∃ i : FiveSector, ∀ j : M.ExtendedCutPiece F, M.cutPieceLabel F covered j = c →
      M.cutPieceLast F j - M.cutPieceFirst F j ∈ closedFiveSector t i := by
  classical
  by_cases attached : ∃ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
      M.cutPieceLabel F covered (Sum.inl e) = c
  · obtain ⟨e, at_c⟩ := attached
    exact ⟨Sum.inl (K.sourceSectorLabel t origin e.val),
      M.cut_component_directions_of_parent F covered positive small e c at_c⟩
  · let u := (F.componentTail c).tip - origin
    obtain ⟨i, a, b, anonnegative, bnonnegative, representation⟩ :=
      exists_mem_closedFiveSector positive small u
    refine ⟨i, fun j same => ?_⟩
    cases j with
    | inl e => exact (attached ⟨e, same⟩).elim
    | inr d =>
      change d = c at same
      subst d
      obtain ⟨r, nonnegative, direction⟩ :=
        (F.componentTail c).direction_eq_nonneg_smul_of_mem (F.componentTail c).tip_mem
      change (F.componentTail c).tip - F.componentSeed c = r • u at direction
      refine ⟨r * a, r * b, mul_nonneg nonnegative anonnegative,
        mul_nonneg nonnegative bnonnegative, ?_⟩
      change (F.componentTail c).tip - F.componentSeed c = _
      rw [direction, representation, smul_add, smul_smul, smul_smul]

end Unfoldings.ConvexRoof.SectorForest
