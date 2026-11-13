module

public import Unfoldings.Roof.RadialComponentFineAncestry
public import Unfoldings.Cap.EnclosingBankSegments

/-! Derive an actual incoming fine edge and its positive enclosing-ray coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (w z : FineC.Vertex Set.univ) (c : F.Component)
  (unattached : ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)
  (member : Q.projectedVertex w ∈ (F.componentTail c).carrier)
  (terminal : Q.projectedVertex z ∈ (F.componentTail c).carrier)

include unattached member terminal

theorem unattached_component_incoming_boundary_bank
    (positive : 0 < t) (small : t < 1) (outward : R.Outward) (i : FiveSector)
    (inside : Q.projectedVertex w - origin ∈ closedFiveSector t i)
    (nonroot : z ∉ R.spanningCompletion.parents.roots)
    (ancestor : R.spanningCompletion.parents.Ancestor w z) (different : w ≠ z)
    (upper : Bool) {h : ℝ} (height_positive : 0 < h)
    (on_bank : (fiveSectorFrame t positive small i).place
      (Q.projectedVertex z - origin) =
      (if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
        else (fiveSectorFrame t positive small i).enclosingStrip.lower).point h) :
    ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
      R.spanningCompletion.parents.parent e.val = z ∧
      R.spanningCompletion.parents.Ancestor w e.val ∧
      Q.projectedVertex e.val ∈ M.extendedGeometricCuts F ∧
      Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
        Q.projectedVertex e.val ∈ closedFiveSector t i ∧
      ∃ b ∈ Set.Ioo (0 : ℝ) h,
        origin + (fiveSectorFrame t positive small i).place.symm
          ((if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
            else (fiveSectorFrame t positive small i).enclosingStrip.lower).point b) =
          Q.projectedVertex e.val := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  obtain ⟨e, parent, reaches, position, on_cuts⟩ :=
    M.unattached_component_exists_incoming_edge F covered R w z c unattached member
      nonroot ancestor different
  have direction := M.unattached_component_nonroot_ancestor_direction F covered R w c
    unattached member positive small outward i inside e reaches
  obtain ⟨a, apositive, scale⟩ :=
    (F.componentTail c).exists_pos_smul_sub_eq_of_members terminal position
  let b := (frame.place (Q.projectedVertex e.val - origin)).re +
    (frame.place (Q.projectedVertex e.val - origin)).im
  have bank : 0 < b ∧ frame.place (Q.projectedVertex e.val - origin) =
      H.point b := by
    cases upper
    · exact frame.enclosingStrip_lower_point_of_pos_scale apositive height_positive on_bank scale
    · exact frame.enclosingStrip_upper_point_of_pos_scale apositive height_positive on_bank scale
  have parent_height :
      (frame.place (Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
        origin)).re +
      (frame.place (Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
        origin)).im = h := by
    rw [parent, on_bank]
    exact H.point_height h
  have quadrant := frame.quadrant_self direction
    (R.completed_parent_direction_ne_zero e.val e.property)
  have delta : Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
      Q.projectedVertex e.val =
      (Q.projectedVertex (R.spanningCompletion.parents.parent e.val) - origin) -
        (Q.projectedVertex e.val - origin) := by abel
  rw [delta, map_sub, Complex.sub_re, Complex.sub_im] at quadrant
  have before : b < h := by
    dsimp only [b]
    linarith [quadrant.1, quadrant.2]
  refine ⟨e, parent, reaches, on_cuts, direction, b, ⟨bank.1, before⟩, ?_⟩
  have equal := congrArg frame.place.symm bank.2
  rw [frame.place.symm_apply_apply] at equal
  change origin + frame.place.symm (H.point b) = _
  rw [← equal, add_sub_cancel]

end Unfoldings.ConvexRoof.SectorForest
