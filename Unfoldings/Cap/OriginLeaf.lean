module

public import Unfoldings.Cap.BankSegments

/-!
# The distinguished sector origin is a forest leaf

Every original nonroot parent step enters its sector strictly, while every
internal original vertex starts in that sector's closure. No parent step can
therefore end at the sector origin. If the origin is internal, its descendant
subtree is a singleton and its actual two child-bank endpoints coincide.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

theorem nonroot_parent_ne_origin (nonnegative : 0 ≤ t) (small : t < 1)
    (v : C.Vertex Set.univ) (nonroot : v ∉ M.parents.roots) : M.parents.parent v ≠ origin := by
  have internal : ¬ C.IsBoundaryVertex Set.univ v := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  have position := mem_closedThreeSector_label_of_backward nonnegative small
    (p := K.projectedVertex v - K.projectedVertex origin)
    (sub_nonpos.mpr (M.maximal v internal))
  have strict := add_mem_strictThreeSector position (M.direction v nonroot)
  have sum : (K.projectedVertex v - K.projectedVertex origin) +
      (K.projectedVertex (M.parents.parent v) - K.projectedVertex v) =
      K.projectedVertex (M.parents.parent v) - K.projectedVertex origin := by abel
  rw [sum] at strict
  intro equal
  rw [equal, sub_self] at strict
  change 0 < threeSectorCoordinates t (K.sourceSectorLabel t origin v) 0 0 ∧ _ at strict
  simp only [map_zero, PiLp.zero_apply, lt_self_iff_false, false_and] at strict

theorem parent_ne_internal_origin (nonnegative : 0 ≤ t) (small : t < 1)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin) (v : C.Vertex Set.univ) :
    M.parents.parent v ≠ origin := by
  by_cases root : v ∈ M.parents.roots
  · rw [M.parents.fixed_root v root]
    intro same
    subst v
    exact internal (by simpa only [M.roots_eq, Set.mem_ofPred_eq] using root)
  · exact M.nonroot_parent_ne_origin nonnegative small v root

theorem ancestor_origin_iff (nonnegative : 0 ≤ t) (small : t < 1)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin) (v : C.Vertex Set.univ) :
    M.parents.Ancestor v origin ↔ v = origin := by
  constructor
  · rintro ⟨n, same⟩
    cases n with
    | zero => exact same
    | succ n =>
      rw [Function.iterate_succ_apply'] at same
      exact (M.parent_ne_internal_origin nonnegative small internal _ same).elim
  · rintro rfl
    exact M.parents.ancestor_refl _

theorem descendants_origin (nonnegative : 0 ≤ t) (small : t < 1)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin) :
    M.parents.descendants origin = {origin} := by
  classical
  ext v
  simp only [M.parents.mem_descendants, M.ancestor_origin_iff nonnegative small internal,
    Finset.mem_singleton]

theorem subtreeCurvature_origin (nonnegative : 0 ≤ t) (small : t < 1)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin) :
    M.subtreeCurvature origin = C.interiorAngularDefect Set.univ origin := by
  classical
  rw [subtreeCurvature, M.descendants_origin nonnegative small internal, Finset.sum_singleton]

/-- At the origin leaf, the two actual bank segments start at one common developed child point. -/
theorem origin_bank_child_points_eq (nonnegative : 0 ≤ t) (small : t < 1)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin) (D : FacewiseDevelopment C M.retain)
    (nonroot : origin ∉ M.parents.roots) :
    M.parentEntrancePoint D ⟨origin, nonroot⟩ 1 = M.parentExitPoint D ⟨origin, nonroot⟩ 1 := by
  classical
  have gap := M.matched_bank_gap_eq D ⟨origin, nonroot⟩ 1
  have empty : (∑ v ∈ Finset.univ.erase (⟨origin, nonroot⟩ :
      {v : C.Vertex Set.univ // v ∉ M.parents.roots}),
      if M.parents.Ancestor v.val origin then
        M.parentExitVector D v - M.parentEntryVector D v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v member
    apply ite_eq_right
    intro ancestor
    have same := (M.ancestor_origin_iff nonnegative small internal v.val).mp ancestor
    exact (Finset.mem_erase.mp member).1 (Subtype.ext same)
  rw [empty, sub_self, zero_smul, add_zero] at gap
  exact (sub_eq_zero.mp gap).symm

end Unfoldings.ConvexCap.SectorForest
