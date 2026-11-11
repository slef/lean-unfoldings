module

public import Unfoldings.Cap.ClipIntrinsicBoundary

/-!
# The assembled roof clip is a genuine geometric convex cap

Translate the clipping height to zero. The actual spatial isometries, supporting
normals, convex footprint, injective projection, horizontal boundary banks, and
nonnegative corner heights satisfy the full geometric cap interface. No acute
triangulation or cutting certificate is asserted.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance clippedCapIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Move the actual clipping plane to height zero by a single ambient isometry. -/
def normalizedFolding : SpatialFolding T.pairedComplex where
  place i := (AffineIsometryEquiv.vaddConst ℝ (Cap.horizontalAtHeight 0 (-Z))).toAffineIsometry.comp
    (T.placement i)
  joined s x := congrArg (fun z : Space => z + Cap.horizontalAtHeight 0 (-Z))
    (T.pairedFolding.joined s x)

theorem normalized_place (i : T.Index) (x : Plane) :
    T.normalizedFolding.place i x = T.placement i x + Cap.horizontalAtHeight 0 (-Z) := rfl

theorem horizontal_add_shift (z : Space) :
    Cap.horizontal (z + Cap.horizontalAtHeight 0 (-Z)) = Cap.horizontal z := by
  rw [map_add, Cap.horizontal_horizontalAtHeight, add_zero]

theorem height_add_shift (z : Space) :
    (z + Cap.horizontalAtHeight 0 (-Z)) 2 = z 2 - Z := by
  rw [PiLp.add_apply, Cap.height_horizontalAtHeight, sub_eq_add_neg]

theorem normalized_toSpace (x : T.pairedComplex.Realization Set.univ) :
    T.normalizedFolding.toSpace Set.univ x =
      T.pairedFolding.toSpace Set.univ x + Cap.horizontalAtHeight 0 (-Z) := by
  obtain ⟨⟨i, x⟩, rfl⟩ :=
    MetricGluing.point_surjective T.pairedComplex.Cell (T.pairedComplex.glue Set.univ) x
  rfl

theorem normalized_surface : T.normalizedFolding.surface =
    (fun z : Space => z + Cap.horizontalAtHeight 0 (-Z)) '' K.clippedRoof Z := by
  rw [← T.pairedFolding_surface]
  ext z
  constructor
  · intro member
    change z ∈ ⋃ i, T.normalizedFolding.place i '' (T.triangle i).carrier at member
    obtain ⟨i, part⟩ := Set.mem_iUnion.mp member
    obtain ⟨x, hx, rfl⟩ := part
    exact ⟨T.placement i x, Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, member, rfl⟩
    change z ∈ ⋃ i, T.placement i '' (T.triangle i).carrier at member
    obtain ⟨i, part⟩ := Set.mem_iUnion.mp member
    obtain ⟨x, hx, rfl⟩ := part
    exact Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩

theorem normalized_footprint : Cap.horizontal '' T.normalizedFolding.surface =
    K.clipFootprint Z := by
  rw [T.normalized_surface, Set.image_image]
  have function_eq : (fun z : Space => Cap.horizontal (z + Cap.horizontalAtHeight 0 (-Z))) =
      Cap.horizontal := by funext z; exact horizontal_add_shift z
  rw [function_eq]
  ext p
  constructor
  · rintro ⟨z, member, rfl⟩
    exact K.horizontal_mem_clip_of_mem_clippedRoof member
  · intro member
    exact ⟨K.roofPoint p, K.roofPoint_mem_clippedRoof member, K.horizontal_roofPoint p⟩

/-- A constructed conforming clip satisfies the entire geometric convex-cap interface. -/
def normalizedCap (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0) :
    ConvexCap T.pairedComplex where
  folding := T.normalizedFolding
  normal := T.normal
  normal_unit := T.normal_unit
  normal_upward := T.normal_upward
  normal_tangent i x := by
    change inner ℝ (T.normal i) ((T.placement i).linear x) = 0
    exact T.normal_tangent i x
  supporting i j x := by
    change inner ℝ (K.normal (T.face i))
      ((T.placement j x.val + Cap.horizontalAtHeight 0 (-Z)) -
        (T.placement i 0 + Cap.horizontalAtHeight 0 (-Z))) ≤ 0
    rw [add_sub_add_right_eq_sub, inner_sub_right, T.placement_eq_roofPoint j x.property]
    exact sub_nonpos.mpr (K.roofPoint_support _ (T.face i))
  projection_injective x y equal := by
    apply (T.pairedFootprintHomeomorph conforming).injective
    apply Subtype.ext
    change Cap.horizontal (T.pairedFolding.toSpace Set.univ x) =
      Cap.horizontal (T.pairedFolding.toSpace Set.univ y)
    change Cap.horizontal (T.normalizedFolding.toSpace Set.univ x) =
      Cap.horizontal (T.normalizedFolding.toSpace Set.univ y) at equal
    simpa only [T.normalized_toSpace, horizontal_add_shift] using equal
  convex_projection := by rw [T.normalized_footprint]; exact K.convex_clipFootprint Z
  interior_projection := by rw [T.normalized_footprint]; exact K.clip_interior_nonempty lower
  rim_horizontal bank x := by
    rw [T.normalized_place, height_add_shift, T.bank_height conforming lower bank x, sub_self]
  corners_above i k := by
    rw [T.normalized_place, height_add_shift]
    have member := (T.triangle i).vertex_mem k
    have projected := T.projected_member i member
    have in_clip := T.cover.symm.subset (Set.mem_iUnion.mpr ⟨i, projected⟩)
    change 0 ≤ T.placement i ((T.triangle i).vertex k) 2 - Z
    rw [T.placement_eq_roofPoint i member, K.height_roofPoint]
    exact sub_nonneg.mpr in_clip

/-- The geometric extension retains the supplied normal-height and tilt estimates exactly. -/
theorem normalizedCap_tiltBound (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) {φ : ℝ} (bound : K.TiltBound φ) :
    (T.normalizedCap conforming lower).TiltBound φ := fun i => bound (T.face i)

theorem normalizedCap_footprint (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) : (T.normalizedCap conforming lower).footprint = K.clipFootprint Z :=
  T.normalized_footprint

end Unfoldings.ConvexCap.ClipSpatialTriangles
