module

public import Unfoldings.Geometry.RadialTriangleMultiplicity
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Consistent triangle orientations put the two opposite corners on different sides of their edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Module

local notation "std" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)

/-- Read the opposite edge first, in the cyclic order inherited from the face. -/
def radialEdgeOrder (e : Fin 3) : Equiv.Perm (Fin 3) :=
  if e = 0 then finRotate 3 else if e = 1 then (finRotate 3).trans (finRotate 3) else Equiv.refl _

private theorem radialEdgeOrder_zero (e : Fin 3) : radialEdgeOrder e 0 = finRotate 3 e := by
  fin_cases e <;> rfl

private theorem radialEdgeOrder_one (e : Fin 3) :
    radialEdgeOrder e 1 = finRotate 3 (finRotate 3 e) := by
  fin_cases e <;> rfl

private theorem radialEdgeOrder_two (e : Fin 3) : radialEdgeOrder e 2 = e := by
  fin_cases e <;> rfl

private theorem radialEdgeOrder_det (v : Fin 3 → Space) (e : Fin 3) :
    (std).det (v ∘ radialEdgeOrder e) = (std).det v := by
  have zero : v ∘ radialEdgeOrder 0 = ![v 1, v 2, v 0] := by
    funext i
    fin_cases i <;> rfl
  have one : v ∘ radialEdgeOrder 1 = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  fin_cases e
  · change (std).det (v ∘ radialEdgeOrder 0) = _
    rw [zero, Basis.det_apply, Basis.det_apply, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    norm_num
    ring
  · change (std).det (v ∘ radialEdgeOrder 1) = _
    rw [one, Basis.det_apply, Basis.det_apply, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    norm_num
    ring
  · rfl

/-- The determinant for one aligned reindexing is negated by reversing its first edge. -/
private theorem standard_det_swap01 (v : Fin 3 → Space) :
    (std).det (v ∘ Equiv.swap 0 1) = -(std).det v := by
  rw [Basis.det_apply, Basis.det_apply, Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)]
  ring

/-- Reversing the shared edge of two consistently oriented triangle bases
gives the transverse scale and preserves the strict open edge. -/
theorem radialEdge_opposite_of_consistent_orientation
    (b c : Basis (Fin 3) ℝ Space) (e f : Fin 3)
    (b_negative : (std).det b < 0) (c_negative : (std).det c < 0)
    (first : b (finRotate 3 e) = c (finRotate 3 (finRotate 3 f)))
    (last : b (finRotate 3 (finRotate 3 e)) = c (finRotate 3 f)) :
    (∀ p, OnOpenRadialEdge b e p → OnOpenRadialEdge c f p) ∧
      ∃ s < (0 : ℝ), ∀ p, b.coord e p = s * c.coord f p := by
  let E := radialEdgeOrder e
  let F := (Equiv.swap 0 1).trans (radialEdgeOrder f)
  let B := b.reindex E.symm
  let C := c.reindex F.symm
  have B_at (i : Fin 3) : B i = b (E i) := by simp [B]
  have C_at (i : Fin 3) : C i = c (F i) := by simp [C]
  have B₂ : E 2 = e := radialEdgeOrder_two e
  have C₂ : F 2 = f := by
    change radialEdgeOrder f ((Equiv.swap 0 1) 2) = f
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
    exact radialEdgeOrder_two f
  have b₀ : B 0 = C 0 := by
    rw [B_at, C_at]
    simpa only [E, F, Equiv.trans_apply, Equiv.swap_apply_left,
      radialEdgeOrder_zero, radialEdgeOrder_one] using first
  have b₁ : B 1 = C 1 := by
    rw [B_at, C_at]
    simpa only [E, F, Equiv.trans_apply, Equiv.swap_apply_right,
      radialEdgeOrder_zero, radialEdgeOrder_one] using last
  have signB : (std).det B < 0 := by
    rw [show (B : Fin 3 → Space) = b ∘ E from funext B_at, radialEdgeOrder_det]
    exact b_negative
  have signC : 0 < (std).det C := by
    rw [show (C : Fin 3 → Space) = (c ∘ radialEdgeOrder f) ∘ Equiv.swap 0 1 from funext C_at,
      standard_det_swap01, radialEdgeOrder_det]
    exact neg_pos.mpr c_negative
  have coefficient : B.det C = B.coord 2 (C 2) := by
    rw [Basis.det_apply, Matrix.det_fin_three]
    simp only [Basis.toMatrix_apply, ← b₀, ← b₁, B.repr_self, Finsupp.single_apply,
      Basis.coord_apply]
    norm_num
  have scale : B.coord 2 (C 2) < 0 := by
    have product := (std).det_mul_det B C
    rw [coefficient] at product
    by_contra! nonnegative
    exact signC.not_ge (product ▸ mul_nonpos_of_nonpos_of_nonneg signB.le nonnegative)
  have projected_B (i : Fin 3) (p : Space) : B.coord i p = b.coord (E i) p := by
    simp [B, Basis.coord_apply]
  have projected_C (i : Fin 3) (p : Space) : C.coord i p = c.coord (F i) p := by
    simp [C, Basis.coord_apply]
  have ratio (p : Space) : B.coord 2 p = B.coord 2 (C 2) * C.coord 2 p :=
    triangle_coord_two_of_common_edge B C b₀ b₁ p
  refine ⟨?_, B.coord 2 (C 2), scale, ?_⟩
  · intro p hp
    have at_B₂ : B.coord 2 p = 0 := by rw [projected_B, B₂, hp.1]
    have at_C₂ : C.coord 2 p = 0 :=
      (mul_eq_zero.mp ((ratio p).symm.trans at_B₂)).resolve_left scale.ne
    have tangent := triangle_tangent_coords_eq B C b₀ b₁ at_B₂
    refine ⟨by rwa [projected_C, C₂] at at_C₂, fun i different => ?_⟩
    obtain ⟨k, rfl⟩ := F.surjective i
    have hk : k ≠ 2 := fun same => different (by rw [same, C₂])
    have positive : 0 < C.coord k p := by
      fin_cases k
      · change 0 < C.coord 0 p
        rw [tangent.1, projected_B]
        exact hp.2 _ (fun eq => (by decide : (0 : Fin 3) ≠ 2) (E.injective (eq.trans B₂.symm)))
      · change 0 < C.coord 1 p
        rw [tangent.2, projected_B]
        exact hp.2 _ (fun eq => (by decide : (1 : Fin 3) ≠ 2) (E.injective (eq.trans B₂.symm)))
      · exact (hk rfl).elim
    rwa [projected_C] at positive
  · intro p
    simpa only [projected_B, projected_C, B₂, C₂] using ratio p

end Unfoldings
