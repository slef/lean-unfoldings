module

public import Unfoldings.Geometry.RayWindowTrimming
public import Unfoldings.Geometry.ChainInterval

/-! Actual internal source-ray sums agree exactly with local polar variation windows. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The actual intermediate links enumerate the strict finite polar window once each. -/
theorem sum_offset_eq_interiorVariation {n m : ℕ} (variation : Fin n → ℝ)
    (first : ℕ) (fits : first + (m + 2) ≤ n) :
    (∑ k : Fin m, variation ⟨first + 1 + k.val, by omega⟩) =
      interiorVariation variation ⟨first, by omega⟩ ⟨first + m + 1, by omega⟩ := by
  classical
  unfold interiorVariation
  apply Finset.sum_bij (fun k _ => (⟨first + 1 + k.val, by omega⟩ : Fin n))
  · intro k _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change first < first + 1 + k.val ∧ first + 1 + k.val < first + m + 1
    omega
  · intro i _ j _ equal
    apply Fin.ext
    have coordinates := congrArg Fin.val equal
    change first + 1 + i.val = first + 1 + j.val at coordinates
    omega
  · intro k member
    have bounds := (Finset.mem_filter.mp member).2
    change first < k.val ∧ k.val < first + m + 1 at bounds
    let j : Fin m := ⟨k.val - (first + 1), by omega⟩
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change first + 1 + (k.val - (first + 1)) = k.val
    omega
  · intro k _
    rfl

namespace PolygonalChain

variable {n m : ℕ} (P : PolygonalChain ℂ n) (source : ℂ)

/-- Actual planar coordinates of the retained interval, with no reparametrized vertices. -/
def planarWindow (first : ℕ) (fits : first + (m + 2) ≤ n) : PolygonalChain Plane (m + 2) where
  vertex j := Complex.orthonormalBasisOneI.repr (P.vertex ⟨first + j.val, by omega⟩)

/-- The short-window geometric input is exactly the original discrete polar-window quantity. -/
theorem planarWindow_internal_angle_sum (genuine : ∀ i, P.vertex i - source ≠ 0)
    (first : ℕ) (fits : first + (m + 2) ≤ n) :
    (∑ k : Fin m, InnerProductGeometry.angle
      ((P.planarWindow first fits).internalSourceRay
        (Complex.orthonormalBasisOneI.repr source) k.castSucc)
      ((P.planarWindow first fits).internalSourceRay
        (Complex.orthonormalBasisOneI.repr source) k.succ)) =
      interiorVariation (P.polarVariation source) ⟨first, by omega⟩
        ⟨first + m + 1, by omega⟩ := by
  rw [← sum_offset_eq_interiorVariation (P.polarVariation source) first fits]
  apply Finset.sum_congr rfl
  intro k _
  let a : Fin (n + 1) := ⟨first + (k.val + 1), by omega⟩
  let b : Fin (n + 1) := ⟨first + (k.val + 1 + 1), by omega⟩
  let L := Complex.orthonormalBasisOneI.repr
  change InnerProductGeometry.angle (L (P.vertex a) - L source)
    (L (P.vertex b) - L source) = _
  rw [← map_sub, ← map_sub]
  calc
    _ = InnerProductGeometry.angle (P.vertex a - source) (P.vertex b - source) :=
      L.toLinearIsometry.angle_map _ _
    _ = |((P.vertex b - source) / (P.vertex a - source)).arg| := by
      rw [InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg (genuine b) (genuine a)]
    _ = P.polarVariation source ⟨first + 1 + k.val, by omega⟩ := by
      unfold polarVariation
      congr 5 <;> apply Fin.ext <;> dsimp [a, b] <;> omega

end PolygonalChain
end Unfoldings
