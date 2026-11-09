module

public import Unfoldings.Path.Geodesic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Constant-speed subpaths

Affine restriction of the unit-interval parameter gives a path between
any two points of an existing path, in either direction. Geodesics remain
geodesics, including at coincident or reversed parameter endpoints.
-/

@[expose] public section

open scoped ENNReal

namespace Path

def intervalParam (s t u : unitInterval) : unitInterval :=
  ⟨AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ),
    (convex_Icc (0 : ℝ) 1).lineMap_mem s.property t.property u.property⟩

theorem continuous_intervalParam (s t : unitInterval) : Continuous (intervalParam s t) :=
  ((lipschitzWith_lineMap (s : ℝ) (t : ℝ)).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem intervalParam_zero (s t : unitInterval) : intervalParam s t 0 = s := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_zero _ _

@[simp] theorem intervalParam_one (s t : unitInterval) : intervalParam s t 1 = t := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one _ _

theorem edist_intervalParam (s t u v : unitInterval) :
    edist (intervalParam s t u) (intervalParam s t v) = edist s t * edist u v := by
  simp only [edist_dist, Subtype.dist_eq]
  change ENNReal.ofReal (dist (AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ))
    (AffineMap.lineMap (s : ℝ) (t : ℝ) (v : ℝ))) = _
  rw [dist_lineMap_lineMap, ENNReal.ofReal_mul dist_nonneg]
  exact mul_comm _ _

theorem intervalParam_mem_Icc {s t : unitInterval} (ordered : s ≤ t) (u : unitInterval) :
    intervalParam s t u ∈ Set.Icc s t :=
  (convex_Icc (s : ℝ) (t : ℝ)).lineMap_mem ⟨le_rfl, ordered⟩ ⟨ordered, le_rfl⟩ u.property

/-- The inverse affine parameter on a nondegenerate interval. -/
noncomputable def intervalFraction (s t u : unitInterval) (ordered : s < t)
    (inside : u ∈ Set.Icc s t) :
    unitInterval := by
  have gap : 0 < (t : ℝ) - (s : ℝ) := sub_pos.mpr ordered
  refine ⟨((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ)),
    div_nonneg (sub_nonneg.mpr inside.1) gap.le, ?_⟩
  apply (div_le_iff₀ gap).mpr
  simpa only [one_mul] using
    (sub_le_sub_right (show (u : ℝ) ≤ (t : ℝ) from inside.2) (s : ℝ))

theorem intervalParam_fraction (s t u : unitInterval) (ordered : s < t)
    (inside : u ∈ Set.Icc s t) :
    intervalParam s t (intervalFraction s t u ordered inside) = u := by
  apply Subtype.ext
  change AffineMap.lineMap (s : ℝ) (t : ℝ)
    (((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))) = (u : ℝ)
  have gap : (t : ℝ) - (s : ℝ) ≠ 0 := (sub_pos.mpr (show (s : ℝ) < (t : ℝ) from ordered)).ne'
  rw [AffineMap.lineMap_apply_ring', div_mul_cancel₀ _ gap]
  exact sub_add_cancel _ _

theorem intervalFraction_pos (s t u : unitInterval) (ordered : s < t)
    (inside : u ∈ Set.Icc s t) (after : s < u) :
    (0 : unitInterval) < intervalFraction s t u ordered inside := by
  change (0 : ℝ) < ((u : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))
  exact div_pos (sub_pos.mpr after) (sub_pos.mpr ordered)

variable {X : Type*} [TopologicalSpace X] {a b : X}

def subpath (p : Path a b) (s t : unitInterval) : Path (p s) (p t) where
  toFun u := p (intervalParam s t u)
  continuous_toFun := p.continuous.comp (continuous_intervalParam s t)
  source' := by rw [intervalParam_zero]
  target' := by rw [intervalParam_one]

@[simp] theorem subpath_apply (p : Path a b) (s t u : unitInterval) :
    p.subpath s t u = p (intervalParam s t u) := rfl

theorem range_subpath_subset (p : Path a b) (s t : unitInterval) :
    Set.range (p.subpath s t) ⊆ Set.range p := by
  rintro _ ⟨u, rfl⟩
  exact ⟨intervalParam s t u, rfl⟩

end Path

namespace Path

variable {X : Type*} [PseudoEMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.subpath (geodesic : p.IsGeodesic) (s t : unitInterval) :
    (p.subpath s t).IsGeodesic := by
  intro u v
  change edist (p (intervalParam s t u)) (p (intervalParam s t v)) =
    edist (p s) (p t) * edist u v
  rw [geodesic, edist_intervalParam, geodesic s t, mul_assoc]

end Path
