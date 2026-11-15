module

public import Unfoldings.Geometry.PolarWindowInterval
public import Unfoldings.Geometry.GenericRadialSource

/-! Actual polar subwindows inherit their source rays, strict radial progress and genuine links. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n m : ℕ} (P : PolygonalChain ℂ n) (source : ℂ)
  (first : ℕ) (fits : first + (m + 2) ≤ n)

theorem planarWindow_edge (i : Fin (m + 2)) :
    (P.planarWindow first fits).edge i =
      Complex.orthonormalBasisOneI.repr (P.edge ⟨first + i.val, by omega⟩) := by
  change Complex.orthonormalBasisOneI.repr (P.vertex _) -
    Complex.orthonormalBasisOneI.repr (P.vertex _) = _
  rw [← map_sub]
  apply congrArg Complex.orthonormalBasisOneI.repr
  unfold edge
  congr 1

include fits in
theorem planarWindow_internalSourceRay_ne_zero (genuine : ∀ i, P.vertex i - source ≠ 0)
    (i : Fin (m + 1)) :
    (P.planarWindow first fits).internalSourceRay
      (Complex.orthonormalBasisOneI.repr source) i ≠ 0 := by
  change Complex.orthonormalBasisOneI.repr (P.vertex _) -
    Complex.orthonormalBasisOneI.repr source ≠ 0
  rw [← map_sub]
  exact Complex.orthonormalBasisOneI.repr.injective.ne (genuine _) |>.trans_eq (map_zero _)

theorem planarWindow_edge_ne_zero (nonzero : ∀ i, P.edge i ≠ 0) (i : Fin (m + 2)) :
    (P.planarWindow first fits).edge i ≠ 0 := by
  rw [P.planarWindow_edge]
  exact Complex.orthonormalBasisOneI.repr.injective.ne (nonzero _) |>.trans_eq (map_zero _)

theorem planarWindow_initial_dist_pos (genuine : ∀ i, P.vertex i - source ≠ 0) :
    0 < dist (Complex.orthonormalBasisOneI.repr source) ((P.planarWindow first fits).vertex 0) := by
  apply dist_pos.mpr
  intro equal
  apply genuine ⟨first, by omega⟩
  apply sub_eq_zero.mpr
  exact (Complex.orthonormalBasisOneI.repr.injective equal).symm

/-- Original positive scalar products imply strict radial progress on every actual subwindow. -/
theorem planarWindow_strictRadialSource
    (progress : ∀ i, P.edge i ≠ 0 → 0 < inner ℝ (P.vertex i.castSucc - source) (P.edge i)) :
    Complex.orthonormalBasisOneI.repr source ∈ (P.planarWindow first fits).strictRadialSources := by
  let L := Complex.orthonormalBasisOneI.repr
  intro i nonzero
  have old_nonzero : P.edge ⟨first + i.val, by omega⟩ ≠ 0 := by
    intro zero
    apply nonzero
    rw [P.planarWindow_edge, zero, map_zero]
  have gain := progress ⟨first + i.val, by omega⟩ old_nonzero
  rw [P.planarWindow_edge]
  change 0 < inner ℝ (L (P.vertex ⟨first + i.val, by omega⟩) - L source)
    (L (P.edge ⟨first + i.val, by omega⟩))
  rw [← map_sub, L.inner_map_map]
  exact gain

end Unfoldings.PolygonalChain
