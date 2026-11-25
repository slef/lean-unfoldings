module

public import Unfoldings.Roof.AffineFloorParentAngles

/-! The angle excess on a parent edge is preserved, with zero at inserted straight vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {T : FloorMesh family floor extra Z}
  {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance coarseEdgeAngleIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance edgeAngleIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

/-- On an actual child, its parent support is its horizontal affine chart. -/
theorem projectedTriangle_eq_of_parent (f : T.Index) (g : L.mesh.Index) (parent : L.parent g = f) :
    let H := (family (T.support f)).project
    (L.mesh.triangle g).affineImage H.toAffineMap H.injective = L.mesh.projectedTriangle g := by
  let H := (family (T.support f)).project
  have same : L.mesh.support g = T.support f := (L.same_support g).trans (congrArg T.support parent)
  calc
    _ = L.mesh.pairedComplex.affineProjectedTriangle
        (fun j => (family (L.mesh.support j)).project) g := by
      apply Triangle.eq_of_vertex_eq
      intro j
      change H ((L.mesh.triangle g).vertex j) = (family (L.mesh.support g)).project ((L.mesh.triangle g).vertex j)
      rw [same]
    _ = _ := L.mesh.affineProjectedTriangle_eq g

include inside in
open Classical in
set_option maxHeartbeats 1600000 in
/-- At each point of a coarse boundary, the sum of fine intrinsic-minus-projected
angles in that parent equals its original corner contribution at that point. -/
theorem sum_parentAngleExcess_at_boundary (f : T.Index) {p : Plane}
    (boundary : p ∈ frontier (T.projectedTriangle f).carrier) :
    (∑ d : L.mesh.pairedComplex.Corner, if L.parent d.1 = f ∧ (L.mesh.projectedTriangle d.1).vertex d.2 = p
      then (L.mesh.triangle d.1).cornerAngle d.2 - (L.mesh.projectedTriangle d.1).cornerAngle d.2
      else 0) =
    ∑ i : Fin 3, if (T.projectedTriangle f).vertex i = p then
      (T.triangle f).cornerAngle i - (T.projectedTriangle f).cornerAngle i else 0 := by
  let H := (family (T.support f)).project
  let x := H.symm p
  let R := AffineEquiv.refl ℝ Plane
  let has (d : L.mesh.pairedComplex.Corner) :=
    L.parent d.1 = f ∧ (L.mesh.projectedTriangle d.1).vertex d.2 = p
  let at_x (d : L.mesh.pairedComplex.Corner) :=
    L.parent d.1 = f ∧ (L.mesh.triangle d.1).vertex d.2 = x
  have old : (T.triangle f).affineImage H.toAffineMap H.injective = T.projectedTriangle f :=
    T.affineProjectedTriangle_eq f
  have has_iff (d : L.mesh.pairedComplex.Corner) : has d ↔ at_x d := by
    have projected (match_parent : L.parent d.1 = f) :
        (L.mesh.projectedTriangle d.1).vertex d.2 = H ((L.mesh.triangle d.1).vertex d.2) :=
      (congrArg (fun T' : Triangle => T'.vertex d.2) (L.projectedTriangle_eq_of_parent f d.1 match_parent)).symm
    have at_p : H x = p := H.apply_symm_apply p
    constructor
    · rintro ⟨parent, eq⟩
      exact ⟨parent, H.injective ((projected parent).symm.trans (eq.trans at_p.symm))⟩
    · rintro ⟨parent, eq⟩
      exact ⟨parent, (projected parent).trans ((congrArg H eq).trans at_p)⟩
  have old_iff (i : Fin 3) : (T.projectedTriangle f).vertex i = p ↔ (T.triangle f).vertex i = x := by
    have vertex : H ((T.triangle f).vertex i) = (T.projectedTriangle f).vertex i :=
      congrArg (fun U : Triangle => U.vertex i) old
    exact ⟨fun eq => H.injective (vertex.trans (eq.trans (H.apply_symm_apply p).symm)),
      fun eq => vertex.symm.trans ((congrArg H eq).trans (H.apply_symm_apply p))⟩
  have unchanged (U : Triangle) : U.affineImage R.toAffineMap R.injective = U := by
    apply Triangle.eq_of_vertex_eq
    intro j
    rfl
  let phys := ∑ d : L.mesh.pairedComplex.Corner,
    if at_x d then ((L.mesh.triangle d.1).affineImage R.toAffineMap R.injective).cornerAngle d.2 else 0
  let proj := ∑ d : L.mesh.pairedComplex.Corner,
    if at_x d then ((L.mesh.triangle d.1).affineImage H.toAffineMap H.injective).cornerAngle d.2 else 0
  have fine_sum :
      (∑ d : L.mesh.pairedComplex.Corner, if has d then
        (L.mesh.triangle d.1).cornerAngle d.2 - (L.mesh.projectedTriangle d.1).cornerAngle d.2 else 0) =
      phys - proj := by
    unfold phys proj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hit : has d
    · have same : (L.mesh.triangle d.1).affineImage H.toAffineMap H.injective =
          L.mesh.projectedTriangle d.1 := L.projectedTriangle_eq_of_parent f d.1 hit.1
      simp only [hit, (has_iff d).mp hit, ite_true, unchanged, same]
    · simp only [hit, mt (has_iff d).mpr hit, ite_false, sub_zero]
  change (∑ d : L.mesh.pairedComplex.Corner, if has d then
    (L.mesh.triangle d.1).cornerAngle d.2 - (L.mesh.projectedTriangle d.1).cornerAngle d.2 else 0) = _
  rw [fine_sum]
  by_cases old_corner : ∃ i, (T.projectedTriangle f).vertex i = p
  · obtain ⟨i, hi⟩ := old_corner
    have at_old : x = (T.triangle f).vertex i := ((old_iff i).mp hi).symm
    have value (A' : Plane ≃ᵃ[ℝ] Plane) :
        (∑ d : L.mesh.pairedComplex.Corner, if at_x d then
          ((L.mesh.triangle d.1).affineImage A'.toAffineMap A'.injective).cornerAngle d.2 else 0) =
          ((T.triangle f).affineImage A'.toAffineMap A'.injective).cornerAngle i := by
      refine Eq.trans ?_ (L.sum_affine_cornerAngles_over_parent inside f i A')
      apply Finset.sum_congr rfl
      intro d _
      have exact_corner : at_x d ↔ L.subdivision.RefinesCorner d (f, i) := by
        change (L.parent d.1 = f ∧ (L.mesh.triangle d.1).vertex d.2 = x) ↔
          (L.parent d.1 = f ∧ (L.mesh.triangle d.1).vertex d.2 = (T.triangle f).vertex i)
        rw [at_old]
      by_cases occurs : at_x d
      · rw [ite_eq_left occurs, ite_eq_left (exact_corner.mp occurs)]
      · rw [ite_eq_right occurs, ite_eq_right (mt exact_corner.mpr occurs)]
    rw [show phys = _ from value R, show proj = _ from value H, unchanged, old, Finset.sum_eq_single i]
    · rw [ite_eq_left hi]
    · intro j _ different
      exact ite_eq_right (fun same => different ((T.projectedTriangle f).vertex_injective
        (same.trans hi.symm)))
    · simp
  have zero_old :
      (∑ i : Fin 3, if (T.projectedTriangle f).vertex i = p then
        (T.triangle f).cornerAngle i - (T.projectedTriangle f).cornerAngle i else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => ite_eq_right (fun eq => old_corner ⟨i, eq⟩))
  rw [zero_old]
  by_cases new_corner : ∃ d, has d
  · obtain ⟨d, hd⟩ := new_corner
    obtain ⟨parent, at_d⟩ := (has_iff d).mp hd
    have old_carrier : (T.projectedTriangle f).carrier = H '' (T.triangle f).carrier :=
      (congrArg Triangle.carrier old.symm).trans ((T.triangle f).affineImage_carrier H.toAffineMap H.injective)
    have x_boundary : x ∈ frontier (T.triangle f).carrier := by
      rw [old_carrier] at boundary
      change p ∈ frontier (H.toContinuousAffineEquiv.toHomeomorph '' (T.triangle f).carrier) at boundary
      rw [← H.toContinuousAffineEquiv.toHomeomorph.image_frontier] at boundary
      obtain ⟨q, mem, image⟩ := boundary
      have equal : q = x := H.injective (image.trans (H.apply_symm_apply p).symm)
      rwa [← equal]
    have regular : ¬ (T.triangle f).IsVertex x := by
      rintro ⟨i, eq⟩
      exact old_corner ⟨i, (old_iff i).mpr eq⟩
    have value (A' : Plane ≃ᵃ[ℝ] Plane) :
        (∑ e : L.mesh.pairedComplex.Corner, if at_x e then
          ((L.mesh.triangle e.1).affineImage A'.toAffineMap A'.injective).cornerAngle e.2 else 0) = Real.pi := by
      have h := L.sum_affine_cornerAngles_over_parent_edge inside d f parent A'
        (at_d.symm ▸ x_boundary) (at_d.symm ▸ regular)
      simpa only [at_x, at_d] using h
    rw [show phys = Real.pi from value R, show proj = Real.pi from value H, sub_self]
  · have zero (A' : Plane ≃ᵃ[ℝ] Plane) :
        (∑ d : L.mesh.pairedComplex.Corner, if at_x d then
          ((L.mesh.triangle d.1).affineImage A'.toAffineMap A'.injective).cornerAngle d.2 else 0) = 0 :=
      Finset.sum_eq_zero (fun d _ => ite_eq_right (fun occurs => new_corner ⟨d, (has_iff d).mpr occurs⟩))
    rw [show phys = 0 from zero R, show proj = 0 from zero H, sub_self]

end Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement
