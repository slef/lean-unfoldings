module

public import Unfoldings.Cap.ClipRealization
public import Unfoldings.Complex.IntrinsicBoundary

/-! The actual unpaired banks of a conforming roof clip are exactly its horizontal outer rim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance clipBoundaryIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The actual geometric rim agrees with the bank boundary of the intrinsic whole-edge gluing. -/
theorem projected_mem_frontier_iff_bankBoundary
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (x : T.pairedComplex.Realization Set.univ) :
    Cap.horizontal (T.pairedFolding.toSpace Set.univ x) ∈ frontier (K.clipFootprint Z) ↔
      x ∈ T.pairedComplex.bankBoundary Set.univ := by
  have compact : IsCompact (K.clipFootprint Z) := T.cover.symm ▸
    isCompact_iUnion (fun i => (T.projectedTriangle i).compact_carrier)
  obtain ⟨h, _, closed, boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall (K.convex_clipFootprint Z)
      (K.clip_interior_nonempty lower) compact.isBounded
  change h '' frontier (K.clipFootprint Z) = Metric.sphere (0 : Plane) 1 at boundary
  change h '' closure (K.clipFootprint Z) = Metric.closedBall (0 : Plane) 1 at closed
  rw [compact.isClosed.closure_eq] at closed
  let d : T.pairedComplex.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1 :=
    (T.pairedFootprintHomeomorph conforming).trans
      ((h.image (K.clipFootprint Z)).trans (Homeomorph.setCongr closed))
  have norm_iff (p : Plane) : p ∈ frontier (K.clipFootprint Z) ↔ ‖h p‖ = 1 := by
    have image : p ∈ frontier (K.clipFootprint Z) ↔ h p ∈ h '' frontier (K.clipFootprint Z) := by
      constructor
      · intro member
        exact ⟨p, member, rfl⟩
      · rintro ⟨q, member, equal⟩
        exact h.injective equal ▸ member
    rw [image, boundary]
    simp only [Metric.mem_sphere, dist_zero_right]
  rw [norm_iff, T.pairedFolding.bankBoundary_iff_disk_norm_eq_one Set.univ d x]
  rfl

/-- Every actual boundary bank lies in the prescribed horizontal clipping plane. -/
theorem bank_height (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (lower : Z < 0) (bank : T.pairedComplex.BoundaryBank Set.univ)
    (x : (T.triangle bank.val.face).Edge bank.val.edge) :
    T.placement bank.val.face x.val 2 = Z := by
  have boundary : T.pairedComplex.bankMap Set.univ bank x ∈
      T.pairedComplex.bankBoundary Set.univ :=
    Set.mem_iUnion.mpr ⟨bank, x, rfl⟩
  have frontier := (T.projected_mem_frontier_iff_bankBoundary conforming lower
    (T.pairedComplex.bankMap Set.univ bank x)).mpr boundary
  have level := K.roofHeight_eq_level_of_clip_frontier frontier
  change K.roofHeight (K.projectFace (T.face bank.val.face) x.val) = Z at level
  rw [T.placement_eq_roofPoint bank.val.face
    ((T.triangle bank.val.face).edge_subset bank.val.edge x.property), K.height_roofPoint]
  exact level

end Unfoldings.ConvexCap.ClipSpatialTriangles
