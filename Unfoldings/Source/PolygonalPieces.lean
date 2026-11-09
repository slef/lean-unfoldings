module

public import Unfoldings.Source.PolygonalDomain
public import Unfoldings.Geometry.PolyhedralSelection

/-!
# Actual polygonal source-face pieces

The constructed source disk has a finite polygonal cover with disjoint polygon
interiors. Every whole closed polygon has one rigid inverse placement into an
original triangle, and its actual endpoint projection agrees there, including
all boundary points. Thus polygonality and folding compatibility hold together.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open AffineArrangement

theorem exists_finite_source_polygon_pieces :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ L : Set (Plane →ᵃ[ℝ] ℝ), L.Finite ∧ (∀ l ∈ L, l ≠ 0) ∧
        ∃ S : Set (L → Bool), S.Finite ∧
          (∀ signs ∈ S, IsCompact (closedChamber (fun l : L => l.val) signs) ∧
            Convex ℝ (closedChamber (fun l : L => l.val) signs) ∧
            (interior (closedChamber (fun l : L => l.val) signs)).Nonempty ∧
            closedChamber (fun l : L => l.val) signs ⊆ R.domain ∧
            ∃ (f : Face) (A : Plane ≃ᵃⁱ[ℝ] Plane), ∀ z : R.domain,
              z.val ∈ closedChamber (fun l : L => l.val) signs →
                ∃ y : C.Cell f, z.val = A y.val ∧
                  R.projection (P.sourcePathCoordinate_injective R) z = C.faceMap Set.univ f y) ∧
          S.Pairwise (fun a b => Disjoint
            (interior (closedChamber (fun l : L => l.val) a))
            (interior (closedChamber (fun l : L => l.val) b))) ∧
          R.domain = ⋃ signs ∈ S, closedChamber (fun l : L => l.val) signs := by
  let := P.metricSpace
  intro source R
  obtain ⟨B, finite_B, nonzero_B, boundary⟩ := P.exists_finite_source_boundary_equations R
  obtain ⟨M, finite_M, pieces⟩ := P.exists_finite_completed_face_pieces R
  let := finite_M.fintype
  let J := M × Face
  let maps (i : J) : Plane →ᵃ[ℝ] Space :=
    (F.place i.2).toAffineMap.comp i.1.val.symm.toAffineMap
  let inequalities (i : J) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
    ((C.triangle i.2).coord k).comp i.1.val.symm.toAffineMap
  have nonzero (i : J) (k : Fin 3) : inequalities i k ≠ 0 :=
    affine_comp_equiv_ne_zero _ ((C.triangle i.2).coord_ne_zero k) _
  let value (z : R.domain) :=
    F.toSpace Set.univ (R.projection (P.sourcePathCoordinate_injective R) z)
  have continuous_value : Continuous value :=
    (F.toSpace_lipschitz Set.univ).continuous.comp
      (R.continuous_projection (P.sourcePathCoordinate_injective R))
  have selects (z : R.domain) :
      ∃ i : J, value z = maps i z.val ∧ ∀ k, 0 ≤ inequalities i k z.val := by
    obtain ⟨A, member, f, y, developed, image⟩ := pieces z
    refine ⟨(⟨A, member⟩, f), ?_, ?_⟩
    · change F.toSpace Set.univ (R.projection (P.sourcePathCoordinate_injective R) z) =
        F.place f (A.symm z.val)
      rw [image, developed, A.symm_apply_apply, F.toSpace_faceMap]
    · intro k
      change 0 ≤ (C.triangle f).coord k (A.symm z.val)
      rw [developed, A.symm_apply_apply]
      exact (Set.ext_iff.mp (C.triangle f).carrier_eq_nonneg_coord y.val).mp y.property k
  obtain ⟨L, finite_L, nonzero_L, S, finite_S, polygons, disjoint, cover⟩ :=
    exists_polyhedral_selection_cover R.compact_domain (P.sourceDomain_closure_interior R)
      B finite_B nonzero_B boundary maps inequalities nonzero value continuous_value selects
  refine ⟨L, finite_L, nonzero_L, S, finite_S, ?_, disjoint, cover⟩
  intro signs member
  obtain ⟨compact, inside, included, i, formula⟩ := polygons signs member
  refine ⟨compact, convex_closedChamber _ _, inside, included, i.2, i.1.val, ?_⟩
  intro z hz
  obtain ⟨image, feasible⟩ := formula z hz
  have in_triangle : i.1.val.symm z.val ∈ (C.triangle i.2).carrier := by
    rw [(C.triangle i.2).carrier_eq_nonneg_coord]
    exact feasible
  let y : C.Cell i.2 := ⟨i.1.val.symm z.val, in_triangle⟩
  refine ⟨y, (i.1.val.apply_symm_apply z.val).symm, P.embedded ?_⟩
  exact image

end Unfoldings.SpatialFolding.ConvexBoundary
