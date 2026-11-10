module

public import Unfoldings.Geometry.PlanarConeOrientation
public import Unfoldings.Geometry.PlanarConjugation

/-! Adjacent hinge separation suffices for unreduced interval-fan headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {n : ℕ} (ray : Fin (n + 2) → Plane)
  (genuine : ∀ i : Fin (n + 1), orient 0 (ray i.castSucc) (ray i.succ) ≠ 0)
  (adjacent : ∀ k : Fin n, Disjoint
    (strictRayCone (ray k.castSucc.castSucc) (ray k.castSucc.succ))
    (strictRayCone (ray k.succ.castSucc) (ray k.succ.succ)))

include genuine adjacent

/-- Distant wedges can overlap; only adjacent hinges are used. -/
theorem interval_cone_orient_sign_of_adjacent (i : Fin (n + 1)) :
    (0 < orient 0 (ray i.castSucc) (ray i.succ)) ↔
      0 < orient 0 (ray (0 : Fin (n + 1)).castSucc) (ray (0 : Fin (n + 1)).succ) := by
  refine Fin.induction Iff.rfl (fun k previous => ?_) i
  have last : orient 0 (ray k.castSucc.succ) (ray k.succ.succ) ≠ 0 := by
    simpa only [Fin.succ_castSucc] using genuine k.succ
  have disjoint : Disjoint
      (strictRayCone (ray k.castSucc.castSucc) (ray k.castSucc.succ))
      (strictRayCone (ray k.castSucc.succ) (ray k.succ.succ)) := by
    simpa only [Fin.succ_castSucc] using adjacent k
  have product := orient_mul_pos_of_disjoint_strictRayCones (genuine k.castSucc) last disjoint
  simp only [Fin.succ_castSucc] at product
  exact (pos_iff_pos_of_mul_pos product).symm.trans previous

/-- Choose one orthogonal frame in which all actual consecutive turns are positive. -/
theorem exists_positive_interval_frame : ∃ L : Plane ≃ₗᵢ[ℝ] ℂ,
    ∀ i : Fin (n + 1), 0 < (starRingEnd ℂ (L (ray i.castSucc)) * L (ray i.succ)).im := by
  let L : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have cross (x y : Plane) : (starRingEnd ℂ (L x) * L y).im = orient 0 x y := by
    have identity := orient_complex_repr_zero (L x) (L y)
    change orient 0 (L.symm (L x)) (L.symm (L y)) = _ at identity
    simpa only [L.symm_apply_apply] using identity.symm
  by_cases first : 0 < orient 0 (ray (0 : Fin (n + 1)).castSucc)
      (ray (0 : Fin (n + 1)).succ)
  · refine ⟨L, fun i => ?_⟩
    rw [cross]
    exact (interval_cone_orient_sign_of_adjacent ray genuine adjacent i).mpr first
  · refine ⟨planeConjugation.trans L, fun i => ?_⟩
    change 0 < (starRingEnd ℂ (L (planeConjugation (ray i.castSucc))) *
      L (planeConjugation (ray i.succ))).im
    rw [cross, orient_planeConjugation]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt (fun h =>
      first ((interval_cone_orient_sign_of_adjacent ray genuine adjacent i).mp h))) (genuine i))

end Unfoldings
