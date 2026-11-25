module

public import Unfoldings.FewestNets.SphericalSelectorFrames
public import Unfoldings.FewestNets.SingleCellCentralMembership

/-! A central hit gives one transverse side and exactly its halfspace on the cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SphericalSelectorBoundary.MetricData

open SpatialRotation Real InnerProductGeometry MeasureTheory

variable {J : Type*} {region : Set Space} {B : SphericalSelectorBoundary J region}
  (M : MetricData B)

theorem mapped_side (T : Space ≃ₗᵢ[ℝ] Space) (j : J) :
    T '' networkEdge B.endpoint j = networkEdge (B.map T).endpoint j :=
  image_closedMinorArc_linearIsometry T _ _

/-- A central side excludes every other placed side, including its endpoints. -/
theorem disjoint_other_side_of_mem_centralSet (cell : Set Space) {d : ℝ} (nonneg : 0 ≤ d)
    (small : d < M.separation) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    {b : Bool} {g : SpatialRotation} {j k : J}
    (central : g ∈ M.centralSet cell d b j) (different : j ≠ k) :
    Disjoint (networkEdge (B.map (orthogonalIsometry g b)).endpoint k) cell := by
  let T := orthogonalIsometry g b
  let moved := B.map T
  let metric := M.map T
  obtain ⟨x, side, contact, reaches⟩ := (M.mem_centralSet_iff cell nonneg b j g).mp central
  have on_side : T x ∈ networkEdge moved.endpoint j :=
    (mapped_side (B := B) T j).subset (Set.mem_image_of_mem T side)
  apply centralSide_disjoint_other_network_edges moved.endpoint moved.endpoint_unit metric.side_pos
    metric.longest_pos metric.longest_small metric.side_le small metric.separated metric.corner
    metric.corner_pos metric.incident cell diameter on_side contact _ different
  intro a
  change M.endpointFactor j a * d < angle (T (B.endpoint j a)) (T x)
  exact (reaches a).trans_eq (T.toLinearIsometry.angle_map _ _).symm

/-- The central events for a small cell are pairwise disjoint in either orientation class. -/
theorem pairwise_disjoint_centralSets (cell : Set Space) {d : ℝ} (nonneg : 0 ≤ d)
    (small : d < M.separation) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    (b : Bool) : Pairwise fun j k => Disjoint (M.centralSet cell d b j) (M.centralSet cell d b k) := by
  intro j k ne
  apply Set.disjoint_left.mpr
  intro g first second
  obtain ⟨x, side, contact, _⟩ := (M.mem_centralSet_iff cell nonneg b k g).mp second
  exact Set.disjoint_left.mp (M.disjoint_other_side_of_mem_centralSet cell nonneg small diameter first ne)
    ((mapped_side (B := B) (orthogonalIsometry g b) k).subset (Set.mem_image_of_mem _ side)) contact

/-- Throughout the small Gaussian cell, membership is the sign of the
single central side's inward form. -/
theorem mem_placed_iff_positive_of_centralSet [Finite J] (cell : Set Space)
    (convex : SphericalConvex cell) {d : ℝ} (nonneg : 0 ≤ d)
    (small : d < M.separation) (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    {b : Bool} {g : SpatialRotation} {j : J} (central : g ∈ M.centralSet cell d b j)
    {y : Space} (in_cell : y ∈ cell) (generic : B.form j ((orthogonalIsometry g b).symm y) ≠ 0) :
    y ∈ orthogonalIsometry g b '' region ↔ 0 < B.form j ((orthogonalIsometry g b).symm y) := by
  let T := orthogonalIsometry g b
  let moved := B.map T
  have equation (z : Space) (k : J) : moved.form k z = B.form k (T.symm z) := rfl
  obtain ⟨x, at_side, contact, _⟩ := (M.mem_centralSet_iff cell nonneg b j g).mp central
  let p := T x
  have active := moved.side_mem.mp ((mapped_side (B := B) T j).subset
    (Set.mem_image_of_mem T at_side))
  have one_side (z : Space) (hz : z ∈ cell) (support : ∀ k, 0 ≤ moved.form k z)
      (k : J) (zero : moved.form k z = 0) : k = j := by
    by_contra different
    have at_k := moved.side_mem.mpr ⟨(moved.membership z).mpr ⟨convex.1 z hz, support⟩, zero⟩
    exact Set.disjoint_left.mp
      (M.disjoint_other_side_of_mem_centralSet cell nonneg small diameter central (fun same => different same.symm))
      at_k hz
  have nonnegative := ((moved.membership p).mp active.1).2
  have strict (k : J) (ne : k ≠ j) : 0 < moved.form k p :=
    (nonnegative k).lt_of_ne (fun zero => ne (one_side p contact nonnegative k zero.symm))
  change y ∈ T '' region ↔ _
  rw [moved.membership, and_iff_right (convex.1 y in_cell), ← equation y j]
  exact mem_central_selector_iff_positive moved.form convex j contact in_cell active.2 strict one_side generic


/-- The reflection pairs the two central events, fixes the actual placed
side pointwise, and negates the selected support form on pulled-back points. -/
theorem exists_centralSet_flip (cell : Set Space) {d : ℝ} (nonneg : 0 ≤ d) (j : J) :
    ∃ flip : SpatialRotation,
      (∀ g b, g ∈ M.centralSet cell d b j ↔ g * flip ∈ M.centralSet cell d (!b) j) ∧
      (∀ g b x, x ∈ networkEdge B.endpoint j →
        orthogonalIsometry (g * flip) (!b) x = orthogonalIsometry g b x) ∧
      ∀ g b x, B.form j ((orthogonalIsometry (g * flip) (!b)).symm x) =
        -B.form j ((orthogonalIsometry g b).symm x) := by
  let n := (InnerProductSpace.toDual ℝ Space).symm (B.form j).toContinuousLinearMap
  have pairing (x : Space) : inner ℝ n x = B.form j x := InnerProductSpace.toDual_symm_apply
  have nonzero : n ≠ 0 := by
    intro zero
    apply B.form_ne_zero j
    ext x
    change B.form j x = 0
    rw [← pairing, zero, inner_zero_left]
  let R := (ℝ ∙ n)ᗮ.reflection
  obtain ⟨flip, reflects⟩ := exists_plane_reflection_placement nonzero
  have action (g : SpatialRotation) (b : Bool) (x : Space) :
      orthogonalIsometry (g * flip) (!b) x = orthogonalIsometry g b (R x) := by
    simpa only [orthogonalIsometry_apply] using reflects g b x
  have fixes (g : SpatialRotation) (b : Bool) (x : Space) (side : x ∈ networkEdge B.endpoint j) :
      orthogonalIsometry (g * flip) (!b) x = orthogonalIsometry g b x := by
    have zero : inner ℝ n x = 0 := (pairing x).trans (B.side_mem.mp side).2
    have at_wall : x ∈ (ℝ ∙ n)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr zero
    rw [action]
    exact congrArg (orthogonalIsometry g b) (Submodule.reflection_mem_subspace_eq_self at_wall)
  have sign (x : Space) : B.form j (R x) = -B.form j x := by
    have opposite : R n = -n := Submodule.reflection_orthogonalComplement_singleton_eq_neg n
    have move : R (-n) = n := by rw [map_neg, opposite, neg_neg]
    calc
      B.form j (R x) = inner ℝ (R (-n)) (R x) := by rw [move, pairing]
      _ = inner ℝ (-n) x := R.inner_map_map _ _
      _ = -B.form j x := by rw [inner_neg_left, pairing]
  refine ⟨flip, fun g b => ?_, fixes, fun g b x => ?_⟩
  · rw [M.mem_centralSet_iff cell nonneg, M.mem_centralSet_iff cell nonneg]
    constructor <;> rintro ⟨y, side, contact, reaches⟩
    · exact ⟨y, side, (fixes g b y side).symm ▸ contact, reaches⟩
    · exact ⟨y, side, (fixes g b y side) ▸ contact, reaches⟩
  · have inverse : (orthogonalIsometry (g * flip) (!b)).symm x =
        R ((orthogonalIsometry g b).symm x) := by
      apply (orthogonalIsometry (g * flip) (!b)).injective
      rw [LinearIsometryEquiv.apply_symm_apply, action]
      rw [Submodule.reflection_involutive, LinearIsometryEquiv.apply_symm_apply]
    rw [inverse, sign]

end Unfoldings.FewestNets.SphericalSelectorBoundary.MetricData
