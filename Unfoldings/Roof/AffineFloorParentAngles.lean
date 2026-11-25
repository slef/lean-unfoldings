module

public import Unfoldings.Roof.AffineFloorParentPatch
public import Unfoldings.Development.TriangularPatchAngles
public import Unfoldings.Complex.SubdivisionCornerAngles
public import Unfoldings.Geometry.TriangleAffineEquiv

/-! Physical and projected corner weights are conserved over each actual coarse face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {T : FloorMesh family floor extra Z}
  {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance originalAngleIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance childAngleIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

open Classical in
private def parentCornerEquiv (f : T.Index) :
    (L.parentComplex f).Corner ≃ {d : L.mesh.pairedComplex.Corner // L.parent d.1 = f} where
  toFun d := ⟨(d.1.val, d.2), d.1.property⟩
  invFun d := (⟨d.val.1, d.property⟩, d.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
theorem sum_parentCornerAngles_eq_patch (f : T.Index) (H : Plane ≃ᵃ[ℝ] Plane) (x : Plane) :
    let R := L.parentAffineComplex f H
    let D := L.parentAffineDevelopment f H
    (∑ d : L.mesh.pairedComplex.Corner, if L.parent d.1 = f ∧ (L.mesh.triangle d.1).vertex d.2 = x
      then ((L.mesh.triangle d.1).affineImage H.toAffineMap H.injective).cornerAngle d.2 else 0) =
    ∑ d : R.Corner, if D.place d.1 ((R.triangle d.1).vertex d.2) = H x then
      (R.triangle d.1).cornerAngle d.2 else 0 := by
  dsimp only
  let weight (d : L.mesh.pairedComplex.Corner) :=
    if (L.mesh.triangle d.1).vertex d.2 = x then
      ((L.mesh.triangle d.1).affineImage H.toAffineMap H.injective).cornerAngle d.2 else 0
  calc
    _ = ∑ d : L.mesh.pairedComplex.Corner, if L.parent d.1 = f then weight d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases same : L.parent d.1 = f <;> simp only [same, true_and, false_and,
        ite_true, ite_false, weight]
    _ = ∑ d : {d : L.mesh.pairedComplex.Corner // L.parent d.1 = f}, weight d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ d : (L.parentComplex f).Corner, weight (L.parentCornerEquiv f d).val :=
      (Equiv.sum_comp (L.parentCornerEquiv f) (fun d => weight d.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      change weight (d.1.val, d.2) =
        (if H ((L.mesh.triangle d.1.val).vertex d.2) = H (x) then
          ((L.mesh.triangle d.1.val).affineImage H.toAffineMap H.injective).cornerAngle d.2 else 0)
      simp only [weight, H.injective.eq_iff]

include inside in
open Classical in
/-- Every invertible affine metric on an old support plane gives the exact
corresponding angle sum over its fine corners in that same metric. -/
theorem sum_affine_cornerAngles_over_parent (f : T.Index) (i : Fin 3)
    (H : Plane ≃ᵃ[ℝ] Plane) :
    (∑ d : L.mesh.pairedComplex.Corner, if L.subdivision.RefinesCorner d (f, i) then
      ((L.mesh.triangle d.1).affineImage H.toAffineMap H.injective).cornerAngle d.2 else 0) =
      ((T.triangle f).affineImage H.toAffineMap H.injective).cornerAngle i := by
  let D := L.parentAffineDevelopment f H
  let old := (T.triangle f).affineImage H.toAffineMap H.injective
  have exact_sum := D.sum_cornerAngles_at_triangular_patch_corner
    (L.parentAffineDevelopment_injective f H inside) old (L.parentAffineDevelopment_range f H) i
  refine Eq.trans ?_ ((L.sum_parentCornerAngles_eq_patch f H ((T.triangle f).vertex i)).trans exact_sum)
  apply Finset.sum_congr rfl
  intro d _
  have same : L.subdivision.RefinesCorner d (f, i) ↔
      L.parent d.1 = f ∧ (L.mesh.triangle d.1).vertex d.2 = (T.triangle f).vertex i := Iff.rfl
  by_cases at_corner : L.subdivision.RefinesCorner d (f, i)
  · rw [ite_eq_left at_corner, ite_eq_left (same.mp at_corner)]
  · rw [ite_eq_right at_corner, ite_eq_right (mt same.mpr at_corner)]

include inside in
/-- Physical line refinement preserves every original intrinsic corner angle. -/
theorem subdivision_cornerAnglePreserving : L.subdivision.CornerAnglePreserving := by
  classical
  rintro ⟨f, i⟩
  let H := AffineEquiv.refl ℝ Plane
  have unchanged (T : Triangle) : T.affineImage H.toAffineMap H.injective = T := by
    apply Triangle.eq_of_vertex_eq
    intro j
    rfl
  have sum := L.sum_affine_cornerAngles_over_parent inside f i H
  change (∑ d : L.mesh.pairedComplex.Corner, if L.subdivision.RefinesCorner d (f, i) then
    (L.mesh.triangle d.1).cornerAngle d.2 else 0) = (T.triangle f).cornerAngle i
  simpa only [unchanged] using sum

include inside in
open Classical in
/-- The actual horizontal projection also conserves every original corner angle. -/
theorem sum_projected_cornerAngles_over_parent (f : T.Index) (i : Fin 3) :
    (∑ d : L.mesh.pairedComplex.Corner, if L.subdivision.RefinesCorner d (f, i) then
      (L.mesh.projectedTriangle d.1).cornerAngle d.2 else 0) = (T.projectedTriangle f).cornerAngle i := by
  classical
  let H := (family (T.support f)).project
  have old_eq : (T.triangle f).affineImage H.toAffineMap H.injective = T.projectedTriangle f :=
    T.affineProjectedTriangle_eq f
  have sum := L.sum_affine_cornerAngles_over_parent inside f i H
  rw [old_eq] at sum
  refine Eq.trans ?_ sum
  apply Finset.sum_congr rfl
  intro d _
  by_cases refined : L.subdivision.RefinesCorner d (f, i)
  · have same : L.mesh.support d.1 = T.support f :=
      (L.same_support d.1).trans (congrArg T.support refined.1)
    have chart : (L.mesh.triangle d.1).affineImage H.toAffineMap H.injective =
        L.mesh.projectedTriangle d.1 := by
      calc
        _ = (L.mesh.pairedComplex).affineProjectedTriangle
          (fun g => (family (L.mesh.support g)).project) d.1 := by
            apply Triangle.eq_of_vertex_eq
            intro j
            change H ((L.mesh.triangle d.1).vertex j) =
              (family (L.mesh.support d.1)).project ((L.mesh.triangle d.1).vertex j)
            rw [same]
        _ = _ := L.mesh.affineProjectedTriangle_eq d.1
    simp only [refined, ite_true, chart]
  · simp only [refined, ite_false]


include inside in
open Classical in
/-- At an inserted vertex strictly between old corner positions, each
metric on its complete parent patch has straight angle π. -/
theorem sum_affine_cornerAngles_over_parent_edge (d : L.mesh.pairedComplex.Corner)
    (f : T.Index) (parent : L.parent d.1 = f) (H : Plane ≃ᵃ[ℝ] Plane)
    (boundary : (L.mesh.triangle d.1).vertex d.2 ∈ frontier (T.triangle f).carrier)
    (regular : ¬ (T.triangle f).IsVertex ((L.mesh.triangle d.1).vertex d.2)) :
    (∑ e : L.mesh.pairedComplex.Corner,
      if L.parent e.1 = f ∧ (L.mesh.triangle e.1).vertex e.2 = (L.mesh.triangle d.1).vertex d.2
      then ((L.mesh.triangle e.1).affineImage H.toAffineMap H.injective).cornerAngle e.2 else 0) = Real.pi := by
  let R := L.parentAffineComplex f H
  let D := L.parentAffineDevelopment f H
  let x := (L.mesh.triangle d.1).vertex d.2
  let old := (T.triangle f).affineImage H.toAffineMap H.injective
  let g : L.parentPieces f := ⟨d.1, parent⟩
  let w := R.vertexOfCorner Set.univ (g, d.2)
  have position : D.toPlane (R.vertexPoint Set.univ w) = H x := rfl
  have frontier_old : H x ∈ frontier old.carrier := by
    have carrier : old.carrier = H '' (T.triangle f).carrier :=
      (T.triangle f).affineImage_carrier H.toAffineMap H.injective
    rw [carrier]
    change H x ∈ frontier (H.toContinuousAffineEquiv.toHomeomorph '' (T.triangle f).carrier)
    rw [← H.toContinuousAffineEquiv.toHomeomorph.image_frontier]
    exact Set.mem_image_of_mem H boundary
  have generic : ¬ old.IsVertex (H x) := by
    rintro ⟨i, eq⟩
    exact regular ⟨i, H.injective eq⟩
  exact (L.sum_parentCornerAngles_eq_patch f H x).trans
    (D.sum_cornerAngles_at_triangular_patch_edge
      (L.parentAffineDevelopment_injective f H inside) old (L.parentAffineDevelopment_range f H)
      w position frontier_old generic)

end Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement
