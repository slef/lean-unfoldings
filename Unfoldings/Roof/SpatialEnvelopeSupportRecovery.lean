module

public import Unfoldings.Roof.SpatialEnvelopeRoof
public import Unfoldings.Roof.SupportingEnvelope
public import Unfoldings.Geometry.SpatialEnvelopePartition
public import Unfoldings.Geometry.AffineArrangement

/-! A sufficiently large finite clip retains the supporting envelope of the entire roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A)

variable [Finite A]

/-- All sufficiently large clips meet the interior of every original whole support cell. -/
theorem exists_level_capturing_support_cells (lower : ℝ) :
    ∃ level : ℝ, lower < level ∧ ∀ L, level ≤ L → ∀ a,
      (interior (P.footprint a) ∩ interior (clip family (-L))).Nonempty := by
  classical
  let point := fun a => (P.full a).choose
  have member (a : A) : point a ∈ interior (P.footprint a) := (P.full a).choose_spec
  obtain ⟨bound, bounded⟩ :=
    (Set.finite_range (fun a => -height family (point a))).bddAbove
  refine ⟨max lower bound + 1, by linarith [le_max_left lower bound], ?_⟩
  intro L large a
  refine ⟨point a, member a, ?_⟩
  apply AffineEnvelope.mem_interior_clip
  change -L < height family (point a)
  have at_point := bounded (Set.mem_range_self a)
  linarith [le_max_right lower bound]

namespace Triangulation

variable {P} {Z : ℝ} (T : Triangulation family Z)

local instance supportRecoveryIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable (conforming : TriangleFamily.Conforming T.projectedTriangle)
  (inside : (interior (clip family Z)).Nonempty)

/-- A mesh face retains its original affine supporting plane everywhere, beyond the clip. -/
theorem roof_supportHeight (f : T.Index) :
    (T.roof conforming inside).supportHeight f = (family (T.support f)).height := by
  ext p
  rw [ConvexRoof.supportHeight_apply]
  exact ((family (T.support f)).height_formula p).symm

omit conforming inside in
/-- An original affine support active on a whole open patch of the clip occurs in the mesh.
Finite avoidance derives the support match; no correspondence of faces is supplied. -/
theorem exists_support_height_eq_of_open_patch {U : Set Plane} (opened : IsOpen U)
    (nonempty : U.Nonempty) (contained : U ⊆ clip family Z) (f : Plane →ᵃ[ℝ] ℝ)
    (active : ∀ p ∈ U, height family p = f p) :
    ∃ j, (family (T.support j)).height = f := by
  classical
  by_contra absent
  have proper (j : T.Index) : (family (T.support j)).height - f ≠ 0 := by
    exact sub_ne_zero.mpr (fun same => absent ⟨j, same⟩)
  obtain ⟨p, member, regular⟩ :=
    (AffineArrangement.dense_regular (fun j => (family (T.support j)).height - f)
      proper).inter_open_nonempty U opened nonempty
  obtain ⟨j, in_triangle⟩ := Set.mem_iUnion.mp (T.cover.subset (contained member))
  apply regular j
  change (family (T.support j)).height p - f p = 0
  exact sub_eq_zero.mpr ((T.active j p in_triangle).symm.trans (active p member))

omit [Finite A] in
/-- Capturing an open part of every original whole support cell preserves the entire
unbounded roof, including points outside the triangulated finite footprint. -/
theorem roofHeight_eq_whole_height
    (captured : ∀ a, (interior (P.footprint a) ∩ interior (clip family Z)).Nonempty)
    (p : Plane) : (T.roof conforming inside).roofHeight p = height family p := by
  apply le_antisymm
  · have cover : p ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ p
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp cover
    obtain ⟨j, same⟩ := T.exists_support_height_eq_of_open_patch
      (isOpen_interior.inter isOpen_interior) (captured a)
      (fun _ h => interior_subset h.2) (family (P.support a)).height
      (fun z hz => P.active a z (interior_subset hz.1))
    exact ((T.roof conforming inside).roofHeight_le_supportHeight p j).trans_eq
      ((congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f p) ((T.roof_supportHeight conforming inside j).trans
        same)).trans (P.active a p member).symm)
  · obtain ⟨j, active⟩ := (T.roof conforming inside).exists_roofHeight_eq_supportHeight p
    rw [active, T.roof_supportHeight conforming inside j]
    exact AffineEnvelope.height_le _ p (T.support j)

end Triangulation
end Unfoldings.SpatialEnvelope
