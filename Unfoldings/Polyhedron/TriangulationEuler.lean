module

public import Unfoldings.Polyhedron.GaussianVertexAngles
public import Unfoldings.Polyhedron.Closedness
public import Unfoldings.Roof.CurvatureNonnegative

/-! Euler characteristic of the original triangulation from its total Gaussian area. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open MeasureTheory
open scoped BigOperators ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
/-- Each local edge is incident to exactly one seam, and every seam contributes two local edges. -/
theorem two_mul_card_seam_eq_three_mul_card_face :
    2 * Fintype.card C.Seam = 3 * Fintype.card Face := by
  let e : C.Seam × Bool ≃ Face × Fin 3 :=
    Equiv.ofBijective (fun p =>
      let s := C.seamSide p.1 p.2
      (s.face, s.edge)) ⟨?_, ?_⟩
  · have card := Fintype.card_congr e
    simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, mul_comm] using card
  · intro a b equal
    apply C.seamSide_injective
    exact congrArg (fun p : Face × Fin 3 => EdgeRef.mk p.1 p.2) equal
  · rintro ⟨f, j⟩
    obtain ⟨s, b, h⟩ := P.exists_seam_at_edge ⟨f, j⟩
    exact ⟨(s, b), congrArg (fun a : EdgeRef Face => (a.face, a.edge)) h⟩

include P in
/-- The actual sum of intrinsic angular defects is the area of the unit sphere. -/
theorem sum_angular_defect_eq_four_pi :
    (∑ v : C.Vertex Set.univ, (2 * Real.pi - C.totalAngle Set.univ v)) = 4 * Real.pi := by
  let N := P.supportingNormals
  have nonneg (v : C.Vertex Set.univ) : 0 ≤ 2 * Real.pi - C.totalAngle Set.univ v := by
    obtain ⟨q, w, _, _, internal, _, angles⟩ := P.exists_upperRoof_with_full_vertex_star N v
    rw [← angles]
    exact sub_nonneg.mpr ((P.hemisphereRoof N q).totalAngle_le_two_pi w internal)
  have measure_eq (v : C.Vertex Set.univ) : 2 * Real.pi - C.totalAngle Set.univ v =
      (solidAngleMeasure (F.gaussianCone (F.gaussianSiteOfVertex v))).toReal := by
    have eq := congrArg ENNReal.toReal (P.gaussianCell_eq_angular_defect N v)
    rw [F.solidAngle_gaussianCell, ENNReal.toReal_ofReal (nonneg v)] at eq
    exact eq.symm
  simp only [measure_eq]
  have reindex := Equiv.sum_comp P.vertexEquivGaussianSite
    (fun i => (solidAngleMeasure (F.gaussianCone i)).toReal)
  exact reindex.trans (F.sum_gaussianArea P)

include P in
/-- The vertex, seam, and triangle counts of a closed convex triangulation satisfy Euler's formula. -/
theorem triangulation_euler :
    (Fintype.card (C.Vertex Set.univ) : ℤ) - Fintype.card C.Seam + Fintype.card Face = 2 := by
  have area := P.sum_angular_defect_eq_four_pi
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    C.sum_totalAngle] at area
  have angle_count : 2 * (Fintype.card (C.Vertex Set.univ) : ℝ) - Fintype.card Face = 4 := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    linarith only [area, show
      (2 * (Fintype.card (C.Vertex Set.univ) : ℝ) - Fintype.card Face) * Real.pi =
        Fintype.card (C.Vertex Set.univ) * (2 * Real.pi) - Fintype.card Face * Real.pi by ring]
  have angle_int : 2 * (Fintype.card (C.Vertex Set.univ) : ℤ) - Fintype.card Face = 4 := by
    exact_mod_cast angle_count
  have incidence := P.two_mul_card_seam_eq_three_mul_card_face
  omega

end Unfoldings.SpatialFolding.ConvexBoundary
