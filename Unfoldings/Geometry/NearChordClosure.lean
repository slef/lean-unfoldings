module

public import Unfoldings.Geometry.TwoLinkRegularApex
public import Unfoldings.Geometry.PolygonalBankTailGerm

/-! A two-link closure near the chord can be made regular and meet the bank only finitely often. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A segment with one endpoint off an affine line meets the line at most once. -/
theorem subsingleton_segment_inter_affine_zero {a b : Plane} (L : Plane →ᵃ[ℝ] ℝ)
    (off : L b ≠ 0) : (segment ℝ a b ∩ {p | L p = 0}).Subsingleton := by
  rintro p ⟨p_on, hp⟩ q ⟨q_on, hq⟩
  obtain ⟨s, _, rfl⟩ := (segment_eq_image_lineMap ℝ a b).subset p_on
  obtain ⟨t, _, rfl⟩ := (segment_eq_image_lineMap ℝ a b).subset q_on
  change L (AffineMap.lineMap a b s) = 0 at hp
  change L (AffineMap.lineMap a b t) = 0 at hq
  rw [L.apply_lineMap] at hp hq
  have different : L a ≠ L b := by
    intro same
    rw [same, AffineMap.lineMap_same] at hp
    exact off hp
  have time := AffineMap.lineMap_injective ℝ different (hp.trans hq.symm)
  rw [time]

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

local notation "a" => P.vertex 0
local notation "b" => P.vertex (Fin.last n)

/-- A regular two-link connector can be chosen in any open region with
a point strictly between the two horizontal endpoint levels. -/
theorem exists_regular_nearChord_apex_of_ordered (x : Plane →L[ℝ] ℝ)
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, a ≠ point i) (last : ∀ i, b ≠ point i)
    {U : Set Plane} (opens : IsOpen U) (center : ∃ q ∈ U, x a < x q ∧ x q < x b) :
    ∃ c ∈ U,
      x a < x c ∧ x c < x b ∧
      (∀ j, edge j c ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i) ∧
      (Set.range P.path ∩ (segment ℝ b c ∪ segment ℝ c a)).Finite := by
  let region := U ∩ {q | x a < x q ∧ x q < x b}
  have open_region : IsOpen region :=
    opens.inter ((isOpen_lt continuous_const x.continuous).inter (isOpen_lt x.continuous continuous_const))
  obtain ⟨p, hU, hl, hr⟩ := center
  have in_region : p ∈ region := ⟨hU, hl, hr⟩
  let cuts (i : Fin n) := segmentEquation (P.vertex i.castSucc) (P.vertex i.succ)
  let equations := Sum.elim edge cuts
  have nonzero : ∀ k, equations k ≠ 0 :=
    Sum.rec proper (fun i => segmentEquation_ne_zero (P.vertex i.castSucc) (P.vertex i.succ))
  obtain ⟨c, hc, regular, avoids⟩ :=
    P.exists_regular_twoLink_apex point equations nonzero open_region ⟨p, in_region⟩ first last
  refine ⟨c, hc.1, hc.2.1, hc.2.2, (fun j => regular (.inl j)), avoids, ?_⟩
  have finite_link (z : Plane) : (Set.range P.path ∩ segment ℝ z c).Finite := by
    let contact (i : Fin n) := segment ℝ z c ∩ {q | cuts i q = 0}
    have finite_contact : (⋃ i, contact i).Finite := Set.finite_iUnion (fun i =>
      (subsingleton_segment_inter_affine_zero (cuts i) (regular (.inr i))).finite)
    apply ((Set.finite_singleton a).union finite_contact).subset
    rintro q ⟨on_bank, on_link⟩
    rcases P.path_range_eq_segments.subset on_bank with source | on_edge
    · exact Or.inl source
    · obtain ⟨i, member⟩ := Set.mem_iUnion.mp on_edge
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, on_link, segmentEquation_eq_zero member⟩)
  rw [Set.inter_union_distrib_left, segment_symm ℝ c a]
  exact (finite_link b).union (finite_link a)

/-- Choose a bend arbitrarily close to the chord midpoint, within an open
region containing it. Both closing links make strict horizontal progress,
avoid the prescribed marked points, and have only finitely many bank contacts. -/
theorem exists_regular_nearChord_apex (x : Plane →L[ℝ] ℝ) (ordered : x a < x b)
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, a ≠ point i) (last : ∀ i, b ≠ point i)
    {U : Set Plane} (opens : IsOpen U) (center : midpoint ℝ a b ∈ U)
    {ε : ℝ} (positive : 0 < ε) :
    ∃ c ∈ U ∩ Metric.ball (midpoint ℝ a b) ε,
      x a < x c ∧ x c < x b ∧
      (∀ j, edge j c ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i) ∧
      (Set.range P.path ∩ (segment ℝ b c ∪ segment ℝ c a)).Finite := by
  apply P.exists_regular_nearChord_apex_of_ordered x point edge proper first last
    (opens.inter Metric.isOpen_ball)
  let p := midpoint ℝ a b
  have x_p : x p + x p = x a + x b := by
    have eq := congrArg x (midpoint_add_self (R := ℝ) a b)
    simpa only [map_add] using eq
  exact ⟨p, ⟨center, Metric.mem_ball_self positive⟩,
    by linarith only [ordered, x_p], by linarith only [ordered, x_p]⟩

end PolygonalChain

end Unfoldings
