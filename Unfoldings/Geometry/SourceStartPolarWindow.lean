module

public import Unfoldings.Geometry.PlanePolarWindow

/-! Polar window identities omit the initial source vertex as well as the two terminal links. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

/-- Named finite-index bounds avoid private arithmetic proofs in window statements. -/
theorem polar_window_first_lt {N m first : ℕ} (fits : first + (m + 2) ≤ N) : first < N := by omega

theorem polar_window_last_lt {N m first : ℕ} (fits : first + (m + 2) ≤ N) :
    first + m + 1 < N := by omega

/-- The initial vertex may equal the source; only actual internal rays enter the polar sum. -/
theorem planarWindow_internal_angle_sum_of_positive_vertices
    {N m : ℕ} (P : PolygonalChain ℂ N) (source : ℂ)
    (genuine : ∀ i : Fin (N + 1), 0 < i.val → P.vertex i - source ≠ 0)
    (first : ℕ) (fits : first + (m + 2) ≤ N) :
    (∑ k : Fin m, InnerProductGeometry.angle
      ((P.planarWindow first fits).internalSourceRay
        (Complex.orthonormalBasisOneI.repr source) k.castSucc)
      ((P.planarWindow first fits).internalSourceRay
        (Complex.orthonormalBasisOneI.repr source) k.succ)) =
      interiorVariation (P.polarVariation source) ⟨first, polar_window_first_lt fits⟩
        ⟨first + m + 1, polar_window_last_lt fits⟩ := by
  rw [← sum_offset_eq_interiorVariation (P.polarVariation source) first fits]
  apply Finset.sum_congr rfl
  intro k _
  let a : Fin (N + 1) := ⟨first + (k.val + 1), by have bound := k.isLt; omega⟩
  let b : Fin (N + 1) := ⟨first + (k.val + 1 + 1), by have bound := k.isLt; omega⟩
  let L := Complex.orthonormalBasisOneI.repr
  change InnerProductGeometry.angle (L (P.vertex a) - L source)
    (L (P.vertex b) - L source) = _
  rw [← map_sub, ← map_sub]
  calc
    _ = InnerProductGeometry.angle (P.vertex a - source) (P.vertex b - source) :=
      L.toLinearIsometry.angle_map _ _
    _ = |((P.vertex b - source) / (P.vertex a - source)).arg| := by
      rw [InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg
        (genuine b (by change 0 < first + (k.val + 1 + 1); omega))
        (genuine a (by change 0 < first + (k.val + 1); omega))]
    _ = P.polarVariation source ⟨first + 1 + k.val, by have bound := k.isLt; omega⟩ := by
      unfold polarVariation
      congr 5 <;> apply Fin.ext <;> dsimp [a, b] <;> omega

/-- The same source-starting identity holds in every orthonormal frame, including reflection. -/
theorem interval_internal_angle_sum_in_frame_of_positive_vertices {N m : ℕ}
    (P : PolygonalChain Plane N) (L : Plane ≃ₗᵢ[ℝ] ℂ) (source : Plane)
    (genuine : ∀ i : Fin (N + 1), 0 < i.val → P.vertex i - source ≠ 0)
    (first : ℕ) (fits : first + (m + 2) ≤ N) :
    (∑ k : Fin m, InnerProductGeometry.angle
      ((P.interval first (m + 2) fits).internalSourceRay source k.castSucc)
      ((P.interval first (m + 2) fits).internalSourceRay source k.succ)) =
      interiorVariation ((P.inComplexFrame L).polarVariation (L source))
        ⟨first, polar_window_first_lt fits⟩ ⟨first + m + 1, polar_window_last_lt fits⟩ := by
  let Q := P.inComplexFrame L
  have nonzero (i : Fin (N + 1)) (positive : 0 < i.val) : Q.vertex i - L source ≠ 0 := by
    change L (P.vertex i) - L source ≠ 0
    rw [← map_sub]
    exact fun zero => genuine i positive (L.injective (zero.trans (map_zero L).symm))
  rw [← Q.planarWindow_internal_angle_sum_of_positive_vertices (L source) nonzero first fits]
  apply Finset.sum_congr rfl
  intro k _
  let a : Fin (N + 1) := ⟨first + (k.val + 1), by have bound := k.isLt; omega⟩
  let b : Fin (N + 1) := ⟨first + (k.val + 1 + 1), by have bound := k.isLt; omega⟩
  let R := Complex.orthonormalBasisOneI.repr
  change InnerProductGeometry.angle (P.vertex a - source) (P.vertex b - source) =
    InnerProductGeometry.angle (R (L (P.vertex a)) - R (L source))
      (R (L (P.vertex b)) - R (L source))
  rw [← map_sub, ← map_sub, ← map_sub, ← map_sub]
  exact (L.toLinearIsometry.angle_map _ _).symm.trans
    (R.toLinearIsometry.angle_map _ _).symm

end Unfoldings.PolygonalChain
