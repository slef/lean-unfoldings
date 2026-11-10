module

public import Unfoldings.Geometry.ConeOrientation
public import Unfoldings.Geometry.ComplexArea

/-! Consistent orientation along genuine disjoint planar corner cones. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem orient_mul_pos_of_disjoint_strictRayCones {x y z : Plane}
    (first : orient 0 x y ≠ 0) (last : orient 0 y z ≠ 0)
    (separated : Disjoint (strictRayCone x y) (strictRayCone y z)) :
    0 < orient 0 x y * orient 0 y z := by
  let L : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have cross (a b : Plane) : (starRingEnd ℂ (L a) * L b).im = orient 0 a b := by
    have identity := orient_complex_repr_zero (L a) (L b)
    change orient 0 (L.symm (L a)) (L.symm (L b)) = _ at identity
    simpa only [L.symm_apply_apply] using identity.symm
  have mapped : Disjoint (strictRayCone (L x) (L y)) (strictRayCone (L y) (L z)) := by
    change Disjoint (strictRayCone (L.toLinearMap x) (L.toLinearMap y))
      (strictRayCone (L.toLinearMap y) (L.toLinearMap z))
    rw [← L.toLinearMap.image_strictRayCone, ← L.toLinearMap.image_strictRayCone]
    exact (Set.disjoint_image_iff L.injective).mpr separated
  simpa only [cross] using cross_mul_pos_of_disjoint_strictRayCones
    (by simpa only [cross] using first) (by simpa only [cross] using last) mapped

/-- The sign is forced by adjacency, including collinear outer boundary rays. -/
theorem interval_cone_orient_sign {n : ℕ} (ray : Fin (n + 2) → Plane)
    (genuine : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
    (separated : Pairwise (fun i j : Fin (n + 1) => Disjoint
      (strictRayCone (ray i.castSucc) (ray i.succ))
      (strictRayCone (ray j.castSucc) (ray j.succ)))) (i : Fin (n + 1)) :
    (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
      0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ) := by
  refine Fin.induction Iff.rfl (fun k previous => ?_) i
  have different : k.castSucc ≠ k.succ := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castSucc, Fin.val_succ] at values
    omega
  have last : orient 0 (ray k.castSucc.succ) (ray k.succ.succ) ≠ 0 := by
    simpa only [Fin.succ_castSucc] using genuine k.succ
  have disjoint : Disjoint
      (strictRayCone (ray k.castSucc.castSucc) (ray k.castSucc.succ))
      (strictRayCone (ray k.castSucc.succ) (ray k.succ.succ)) := by
    simpa only [Fin.succ_castSucc] using separated different
  have product := orient_mul_pos_of_disjoint_strictRayCones (genuine k.castSucc) last disjoint
  simp only [Fin.succ_castSucc] at product
  exact (pos_iff_pos_of_mul_pos product).symm.trans previous

end Unfoldings
