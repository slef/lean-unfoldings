module

public import Unfoldings.FewestNets.IcosahedronExactFacets
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Exact normal representatives of the supporting chord planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open InnerProductSpace NormedSpace

def rawFacetNormal {q : ℕ} (hq : 0 < q) (t : MeshFace q) : Space :=
  (toDual ℝ Space).symm (meshGauge hq t).toContinuousLinearMap

theorem inner_rawFacetNormal {q : ℕ} (hq : 0 < q) (t : MeshFace q) (x : Space) :
    inner ℝ (rawFacetNormal hq t) x = meshGauge hq t x :=
  toDual_symm_apply

theorem rawFacetNormal_ne_zero {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    rawFacetNormal hq t ≠ 0 := by
  intro zero
  have h := inner_rawFacetNormal hq t (inscribedCorners t 0)
  rw [zero, inner_zero_left, meshGauge_corner] at h
  norm_num at h

def facetNormal {q : ℕ} (hq : 0 < q) (t : MeshFace q) : Space :=
  NormedSpace.normalize (rawFacetNormal hq t)

theorem facetNormal_unit {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    ‖facetNormal hq t‖ = 1 :=
  norm_normalize (rawFacetNormal_ne_zero hq t)

theorem inner_facetNormal {q : ℕ} (hq : 0 < q) (t : MeshFace q) (x : Space) :
    inner ℝ (facetNormal hq t) x = meshGauge hq t x / ‖rawFacetNormal hq t‖ := by
  rw [facetNormal, NormedSpace.normalize, real_inner_smul_left, inner_rawFacetNormal,
    div_eq_inv_mul]

/-- At a corner of its own triangle, every unit outward normal has positive support height. -/
theorem inner_facetNormal_corner_pos {q : ℕ} (hq : 0 < q) (t : MeshFace q) (i : Fin 3) :
    0 < inner ℝ (facetNormal hq t) (inscribedCorners t i) := by
  rw [inner_facetNormal, meshGauge_corner]
  exact div_pos zero_lt_one (norm_pos_iff.mpr (rawFacetNormal_ne_zero hq t))

end Unfoldings.FewestNets.Icosahedron
