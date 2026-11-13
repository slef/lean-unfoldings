module

public import Unfoldings.Roof.Basic
public import Unfoldings.Complex.IntrinsicBoundary
public import Unfoldings.Cap.Basic
public import Unfoldings.Cap.VerticalProduct

/-! Normalize an actual supported roof with a horizontal boundary to the geometric cap interface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Translate the entire spatial folding so the level `Z` becomes height zero. -/
def levelFolding (Z : ℝ) : SpatialFolding C where
  place f := (AffineIsometryEquiv.vaddConst ℝ (Cap.horizontalAtHeight 0 (-Z))).toAffineIsometry.comp
    (K.folding.place f)
  joined s x := congrArg (fun z : Space => z + Cap.horizontalAtHeight 0 (-Z)) (K.folding.joined s x)

theorem levelFolding_toSpace (Z : ℝ) (x : C.Realization Set.univ) :
    (K.levelFolding Z).toSpace Set.univ x =
      K.folding.toSpace Set.univ x + Cap.horizontalAtHeight 0 (-Z) := by
  obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  rfl

theorem horizontal_add_level (Z : ℝ) (z : Space) :
    Cap.horizontal (z + Cap.horizontalAtHeight 0 (-Z)) = Cap.horizontal z := by
  rw [map_add, Cap.horizontal_horizontalAtHeight, add_zero]

theorem height_add_level (Z : ℝ) (z : Space) :
    (z + Cap.horizontalAtHeight 0 (-Z)) 2 = z 2 - Z := by
  rw [PiLp.add_apply, Cap.height_horizontalAtHeight, sub_eq_add_neg]

theorem levelFolding_surface (Z : ℝ) :
    (K.levelFolding Z).surface = (fun z : Space => z + Cap.horizontalAtHeight 0 (-Z)) ''
      K.folding.surface := by
  ext z
  constructor
  · rintro member
    obtain ⟨f, x, hx, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨K.folding.place f x, Set.mem_iUnion.mpr ⟨f, x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, member, rfl⟩
    obtain ⟨f, x, hx, rfl⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨f, x, hx, rfl⟩

theorem levelFolding_footprint (Z : ℝ) :
    Cap.horizontal '' (K.levelFolding Z).surface = K.footprint := by
  rw [K.levelFolding_surface, Set.image_image]
  have same : (fun z : Space => Cap.horizontal (z + Cap.horizontalAtHeight 0 (-Z))) =
      Cap.horizontal := funext (horizontal_add_level Z)
  rw [same]
  rfl

/-- A roof whose actual banks lie at one level and whose corners lie above it is a geometric
convex cap after an ambient translation. Original triangles and seam names are unchanged. -/
def capOfHorizontalLevel (Z : ℝ)
    (boundary : ∀ x ∈ C.bankBoundary Set.univ, K.folding.toSpace Set.univ x 2 = Z)
    (above : ∀ f i, Z ≤ K.folding.place f ((C.triangle f).vertex i) 2) : ConvexCap C where
  folding := K.levelFolding Z
  normal := K.normal
  normal_unit := K.normal_unit
  normal_upward := K.normal_upward
  normal_tangent := K.normal_tangent
  supporting f g x := by
    change inner ℝ (K.normal f) ((K.folding.place g x.val + Cap.horizontalAtHeight 0 (-Z)) -
      (K.folding.place f 0 + Cap.horizontalAtHeight 0 (-Z))) ≤ 0
    rw [add_sub_add_right_eq_sub]
    exact K.supporting f g x
  projection_injective x y same := by
    apply K.projection_injective
    simpa only [K.levelFolding_toSpace, horizontal_add_level] using same
  convex_projection := by rw [K.levelFolding_footprint]; exact K.convex_projection
  interior_projection := by rw [K.levelFolding_footprint]; exact K.interior_projection
  rim_horizontal bank x := by
    change (K.folding.place bank.val.face x.val + Cap.horizontalAtHeight 0 (-Z)) 2 = 0
    rw [height_add_level]
    have at_bank := boundary (C.bankMap Set.univ bank x)
      (C.bankMap_mem_bankBoundary Set.univ bank x)
    change K.folding.place bank.val.face x.val 2 = Z at at_bank
    rw [at_bank, sub_self]
  corners_above f i := by
    change 0 ≤ (K.folding.place f ((C.triangle f).vertex i) + Cap.horizontalAtHeight 0 (-Z)) 2
    rw [height_add_level]
    exact sub_nonneg.mpr (above f i)

end Unfoldings.ConvexRoof
