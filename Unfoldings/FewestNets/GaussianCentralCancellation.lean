module

public import Unfoldings.FewestNets.GaussianCyclicAccounting
public import Unfoldings.FewestNets.GaussianSelectorCrossings
public import Unfoldings.FewestNets.SphericalSelectorCentral

/-! Central intersections cancel the signed charges on the actual Gaussian cycle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory SphericalSelectorBoundary InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {J : Type*} [Finite J] {region : Set Space} {B : SphericalSelectorBoundary J region}
  (M : MetricData B) (a : C.Vertex Set.univ)

local notation "site" => F.gaussianSiteOfVertex a
local notation "cell" => F.gaussianCell site

open Classical in
include P in
set_option maxHeartbeats 1800000 in
/-- Reflect a central side across its own plane. The original Gaussian cell
has cancelling signed charges before and after reflection. -/
theorem ae_gaussian_centralCharge_pair
    (extreme : (site : Space) ∈ F.vertexHull.extremePoints ℝ)
    {d : ℝ} (nonneg : 0 ≤ d) (small : d < M.separation)
    (diameter : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d)
    {first second : C.Seam} (first_side : first ∈ gaussianArcSeams N a)
    (second_side : second ∈ gaussianArcSeams N a)
    (j : J) (flip : SpatialRotation)
    (stable : ∀ g, g ∈ M.centralSet cell d false j ↔ g * flip ∈ M.centralSet cell d true j)
    (negates : ∀ g x, B.form j ((orthogonalIsometry (g * flip) true).symm x) =
      -B.form j ((orthogonalIsometry g false).symm x)) :
    ∀ᵐ g ∂probability, g ∈ M.centralSet cell d false j →
      gaussianSignedCharge N (movedSiteFlag region false g) a first second +
        gaussianSignedCharge N (movedSiteFlag region true (g * flip)) a first second = 0 := by
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link a
  have nonempty := P.nonempty_cyclicRunStarts_of_extreme N c covers extreme
  obtain ⟨m, count⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr nonempty)
  let normal := compressedLinkNormal N c count
  let next := finRotate (m + 1)
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  let edge (i : Fin (m + 1)) := (s (next i)).val
  let markFirst := next.symm (s.symm ⟨first, first_side⟩)
  let markSecond := next.symm (s.symm ⟨second, second_side⟩)
  have name_first : edge markFirst = first := by
    change (s (next (next.symm (s.symm ⟨first, first_side⟩)))).val = first
    rw [next.apply_symm_apply, s.apply_symm_apply]
  have name_second : edge markSecond = second := by
    change (s (next (next.symm (s.symm ⟨second, second_side⟩)))).val = second
    rw [next.apply_symm_apply, s.apply_symm_apply]
  have normal_source (i : Fin (m + 1)) : ∃ f k,
      C.vertexOfCorner Set.univ (f, k) = a ∧ N.normal f = normal i := by
    have member : normal i ∈ Set.range
        (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) := ⟨i, rfl⟩
    rwa [range_compressed_linkNormals N c covers count] at member
  choose face corner at_a represents using normal_source
  have inside (i : Fin (m + 1)) : normal i ∈ cell := by
    rw [← represents i]
    have point := F.normal_mem_gaussianCell_of_corner N (face i) (corner i)
    rwa [at_a i] at point
  have ends (i : Fin (m + 1)) : HasGaussianArcEnds N (edge i) (normal i) (normal (next i)) := by
    have h := P.compressedLinkNormal_arcEnds N c closes covers count (next i)
    change HasGaussianArcEnds N (edge i) (normal (next.symm (next i))) (normal (next i)) at h
    rwa [next.symm_apply_apply] at h
  have generic := ae_orthogonalIsometry_symm_avoids_hyperplanes false N.normal N.unit
    B.form B.form_ne_zero
  have transverse := ae_selector_endpoints_avoid_gaussian_walls (F := F) B a false
  filter_upwards [generic, transverse, P.ae_gaussian_selector_crossing N B a false] with
    g regular transverse crossing central
  let T := orthogonalIsometry g false
  let value (i : Fin (m + 1)) := B.form j (T.symm (normal i))
  have value_ne (i : Fin (m + 1)) : value i ≠ 0 := by
    change B.form j (T.symm (normal i)) ≠ 0
    rw [← represents i]
    exact regular (face i) j
  have stable_hit := (stable g).mp central
  have base (i : Fin (m + 1)) :
      movedSiteFlag region false g (normal i) = decide (0 < value i) := by
    have hp := M.mem_placed_iff_positive_of_centralSet cell
      (sphericalConvex_original_gaussianCell (F := F) a) nonneg small diameter central (inside i)
      (value_ne i)
    have flag := (movedSiteFlag_eq_true_iff region false g (normal i)).trans hp
    by_cases h : 0 < value i
    · exact (flag.mpr h).trans (decide_eq_true h).symm
    · exact (Bool.eq_false_iff.mpr (mt flag.mp h)).trans (decide_eq_false h).symm
  have opposite (i : Fin (m + 1)) :
      movedSiteFlag region true (g * flip) (normal i) = !decide (0 < value i) := by
    have neg_eq : B.form j ((orthogonalIsometry (g * flip) true).symm (normal i)) = -value i :=
      negates g (normal i)
    have hp := M.mem_placed_iff_positive_of_centralSet cell
      (sphericalConvex_original_gaussianCell (F := F) a) nonneg small diameter stable_hit (inside i)
      (by rw [neg_eq, neg_ne_zero]; exact value_ne i)
    rw [neg_eq] at hp
    have flag := (movedSiteFlag_eq_true_iff region true (g * flip) (normal i)).trans hp
    by_cases h : 0 < value i
    · rw [decide_eq_true h, Bool.not_true]
      exact Bool.eq_false_iff.mpr (mt flag.mp (by linarith only [h]))
    · rw [decide_eq_false h, Bool.not_false]
      exact flag.mpr (neg_pos.mpr ((le_of_not_gt h).lt_of_ne (value_ne i)))
  let u := T (B.endpoint j false)
  let v := T (B.endpoint j true)
  have unit_u : ‖u‖ = 1 := (T.norm_map _).trans (B.endpoint_unit j false)
  have unit_v : ‖v‖ = 1 := (T.norm_map _).trans (B.endpoint_unit j true)
  have not_antipodal : u + v ≠ 0 := by
    intro zero
    apply M.side_nonantipodal j
    apply T.injective
    rw [map_add, map_zero]
    exact zero
  have witnesses (i : Fin (m + 1)) (across : value i * value (next i) < 0) :
      (openMinorArc (normal i) (normal (next i)) ∩ openMinorArc u v).Nonempty := by
    have change_flag : movedSiteFlag region false g (normal i) ≠
        movedSiteFlag region false g (normal (next i)) := by
      rw [base i, base (next i)]
      intro same
      have iff_sign : 0 < value i ↔ 0 < value (next i) := decide_eq_decide.mp same
      by_cases first : 0 < value i
      · exact across.not_ge (mul_nonneg first.le (iff_sign.mp first).le)
      · exact across.not_ge (mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt first)
          (le_of_not_gt (mt iff_sign.mpr first)))
    have change_seam : movedSiteFlag region false g (N.normal (C.left (edge i)).face) ≠
        movedSiteFlag region false g (N.normal (C.right (edge i)).face) := by
      rcases ends i with ⟨left, right⟩ | ⟨left, right⟩ <;> rw [left, right]
      · exact change_flag
      · exact change_flag.symm
    have incident : edge i ∈ incidentSeams a := (Finset.mem_filter.mp (s (next i)).property).1
    obtain ⟨k, x, on_seam, on_other, in_cell⟩ := crossing (edge i) incident change_seam
    have equal : k = j := by
      by_contra different
      have disjoint := M.disjoint_other_side_of_mem_centralSet cell nonneg small diameter central
        (show j ≠ k from fun eq => different eq.symm)
      exact Set.disjoint_left.mp disjoint
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ on_other)) in_cell
    subst k
    rw [(ends i).openMinorArc] at on_seam
    exact ⟨x, on_seam, on_other⟩
  have charge := P.gaussian_cycleCharge_pair_of_side_witnesses N c closes covers count
    extreme value value_ne unit_u unit_v not_antipodal
    (fun w different => Or.inl (transverse j false ⟨w, different⟩))
    witnesses markFirst markSecond
  have left_eq : movedSiteFlag region false g ∘ normal = fun i => decide (0 < value i) :=
    funext base
  have right_eq : movedSiteFlag region true (g * flip) ∘ normal = fun i => !decide (0 < value i) :=
    funext opposite
  have left_charge := P.gaussianSignedCharge_eq_cycleCharge N c closes covers count
    (movedSiteFlag region false g) markFirst markSecond
  have right_charge := P.gaussianSignedCharge_eq_cycleCharge N c closes covers count
    (movedSiteFlag region true (g * flip)) markFirst markSecond
  change gaussianSignedCharge N (movedSiteFlag region false g) a (edge markFirst) (edge markSecond) =
    SingleCellCharge.cycleCharge (movedSiteFlag region false g ∘ normal) markFirst markSecond at left_charge
  change gaussianSignedCharge N (movedSiteFlag region true (g * flip)) a (edge markFirst) (edge markSecond) =
    SingleCellCharge.cycleCharge (movedSiteFlag region true (g * flip) ∘ normal) markFirst markSecond at right_charge
  rw [name_first, name_second, left_eq] at left_charge
  rw [name_first, name_second, right_eq] at right_charge
  rwa [left_charge, right_charge]

end Unfoldings.SpatialFolding.ConvexBoundary
