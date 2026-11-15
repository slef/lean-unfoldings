module

public import Unfoldings.Cap.ProcessedContactModels
public import Unfoldings.Complex.ContourContactFans

/-! The original contour determines the actual retained contact fan and its curvature charge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin Q.length)
  (fresh : C.contourOriginalVertex S Q i.succ ∉ (C.contourFrontier S Q i.succ).processed)
  (nonroot : C.contourOriginalVertex S Q i.castSucc ∉ P.roots)

include K roots starts fresh nonroot in
/-- The named preceding original contour corner is the actual newly exposed intermediate
fan. Its completion model uses that exact original angle and charges only original curvature.
No current-copy choice, fan-matching premise or angle-conservation premise is supplied.
Physical placement of the inserted gap is not asserted here. -/
theorem exists_contour_contact_remainder_model :
    let original := C.totalAngle Set.univ (C.contourOriginalVertex S Q i.castSucc)
    let untouched := C.totalAngle (C.selectedRetain S)
      (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc))
    ∃ F : CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)),
      (∀ x : MetricGluing.Total (fun j => PolygonalPoint
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) j)),
        (F (MetricGluing.point _ (MetricGluing.polygonalCoincident
          (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
            x.2.val) ∧
      (2 * Real.pi - untouched) - (original - untouched) =
        C.interiorAngularDefect Set.univ (C.contourOriginalVertex S Q i.castSucc) ∧
      (2 * Real.pi - untouched) - (original - untouched) ≤
        C.totalInteriorAngularDefect Set.univ := by
  have positive : 0 < i.val := by
    by_contra zero
    have at_zero : i.castSucc = 0 := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero]; omega)
    exact nonroot (at_zero ▸ starts)
  let frontier := C.contourFrontier S Q i.succ
  let seed := C.contourOriginalVertex S Q i.succ
  let w := C.vertexForgetCuts
    (C.selectedRetain_subset_processed S (C.contourAfterPosition S Q i.succ))
    (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc))
  have original : C.vertexForgetCuts (Set.subset_univ _) w =
      C.contourOriginalVertex S Q i.castSucc := rfl
  have contact : C.vertexForgetCuts (Set.subset_univ _) w =
      P.parent^[frontier.contactTime seed] seed := by
    rw [original]
    change C.contourOriginalVertex S Q i.castSucc =
      P.parent^[(C.contourFrontier S Q i.succ).contactTime
        (C.contourOriginalVertex S Q i.succ)] (C.contourOriginalVertex S Q i.succ)
    rw [C.fresh_contour_contactTime S roots Q i fresh, Function.iterate_one]
    exact (C.fresh_contour_parent S roots Q i fresh).symm
  have model := K.exists_processed_contact_remainder_model S roots frontier seed fresh w
    (original.symm ▸ nonroot) contact
  have angles := C.contour_contact_fan_totalAngle S Q i positive
  dsimp only
  rw [← angles]
  exact model

end Unfoldings.ConvexCap
