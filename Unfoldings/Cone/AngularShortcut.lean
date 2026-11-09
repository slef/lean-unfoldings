module

public import Unfoldings.Cone.AngularSector
public import Unfoldings.Cone.SectorShortcut
public import Unfoldings.Path.Straight

/-!
# Strict apex shortcuts in convex angular fans

For total angle less than pi, every pair of nonapex points has an intrinsic
chord strictly shorter than the two radial legs. No geodesic between such
endpoints can visit the apex.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem develop_isometry_of_lt_pi (small : A.totalAngle < Real.pi) : Isometry A.develop :=
  (isometry_subtype_coe (s := planarSector A.totalAngle)).comp (A.sectorEquiv_isometry small)

theorem dist_lt_via_origin (small : A.totalAngle < Real.pi) {x y : A.Surface}
    (left_nonzero : x ≠ A.origin) (right_nonzero : y ≠ A.origin) :
    dist x y < dist x A.origin + dist A.origin y := by
  have isometry := A.develop_isometry_of_lt_pi small
  have nonzero (z : A.Surface) (hz : z ≠ A.origin) : A.develop z ≠ 0 := by
    intro zero
    exact hz (isometry.injective (zero.trans A.develop_origin.symm))
  have strict := dist_lt_via_zero_of_mem_planarSector A.totalAngle
    (Real.sin_pos_of_pos_of_lt_pi A.totalAngle_pos small)
    (A.develop_mem_sector small x) (A.develop_mem_sector small y)
    (nonzero x left_nonzero) (nonzero y right_nonzero)
  rw [← A.develop_origin, isometry.dist_eq, isometry.dist_eq, isometry.dist_eq] at strict
  exact strict

theorem geodesic_ne_origin (small : A.totalAngle < Real.pi) {a b : A.Surface} {p : Path a b}
    (geodesic : p.IsGeodesic) (left_nonzero : a ≠ A.origin) (right_nonzero : b ≠ A.origin)
    (t : unitInterval) : p t ≠ A.origin := by
  have isometry := A.develop_isometry_of_lt_pi small
  have saturated : edist (A.develop (p 0)) (A.develop (p 1)) = edist (p 0) (p 1) :=
    isometry.edist_eq _ _
  have between := geodesic.map_mem_segment A.develop A.develop_lipschitz
    (show (0 : unitInterval) ≤ t from t.property.1)
    (show t ≤ (1 : unitInterval) from t.property.2) saturated
  simp only [Path.source, Path.target] at between
  have nonzero (z : A.Surface) (hz : z ≠ A.origin) : A.develop z ≠ 0 := by
    intro zero
    exact hz (isometry.injective (zero.trans A.develop_origin.symm))
  intro through
  rw [through, A.develop_origin] at between
  exact zero_not_mem_segment_of_mem_planarSector A.totalAngle
    (Real.sin_pos_of_pos_of_lt_pi A.totalAngle_pos small)
    (A.develop_mem_sector small a) (A.develop_mem_sector small b)
    (nonzero a left_nonzero) (nonzero b right_nonzero) between

end Unfoldings.AngularFan
