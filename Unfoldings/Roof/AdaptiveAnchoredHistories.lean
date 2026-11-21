module

public import Unfoldings.Roof.AdaptiveGeometricHistories
public import Unfoldings.Roof.AdaptiveParentRadial
public import Unfoldings.Roof.DirectedCutPieces

/-! Every subhistory of the actual adaptive cut forest has the certified radial margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {L : Set Plane} {r margin η : ℝ}
  (R : K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary L r margin η)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (positive : 0 < r) (disk : Metric.closedBall (0 : Plane) r ⊆ L)
  {b : ℝ} (bound_pos : 0 < b) (ratio : r ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)

local notation "R₀" => R.asCommonPotentialRouting positive disk bound_pos ratio upper

include no_boundary in
/-- Two different actual directed carriers join only at the start of the new carrier. -/
theorem directedCutSwitch_first_eq_zero {x y y' z : Plane}
    (S : (R₀).DirectedCutStep x y) (T : (R₀).DirectedCutStep y' z)
    (join : y = y') (different : S.vertex ≠ T.vertex) : T.first = 0 := by
  by_contra different_time
  have new : y ∈ (R₀).openPiece T.vertex :=
    Eq.mpr (congrArg (fun p => p ∈ (R₀).openPiece T.vertex) join)
      (T.first_mem_openPiece (lt_of_le_of_ne T.first_nonneg (Ne.symm different_time)))
  rcases S.last_mem_openPiece_or_vertex with old | ⟨v, equal⟩
  · exact Set.disjoint_left.mp
      (K.compatible_openPieces_pairwise_disjoint compact nonempty (R₀) no_boundary different)
      old new
  · exact K.compatible_openPiece_avoids_vertices compact nonempty (R₀) no_boundary
      T.vertex v (equal ▸ new)

include no_boundary in
set_option linter.style.longLine false in
open Classical in
/-- The actual directed pieces give a radial margin from every earlier bank
vertex, including anchors in the interior of a refined original edge. -/
theorem commonFollows_adaptive_radial_margin
    {n : ℕ} (P : PolygonalChain Plane n) (follows : (R₀).Follows P)
    (nonzero : ∀ i, P.edge i ≠ 0)
    {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (interior_margin : γ ≤ margin) (exterior_margin : γ ≤ η)
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      let G := K.clippedExtension slopes compact nonempty
      let E := G.boundaryEnvelope boundary
      let q := P.vertex j
      let S (i : Fin (n + 1)) : (R₀).DirectedCutStep (P.vertex i.castSucc) (P.vertex i.succ) :=
        Classical.choice ((R₀).nonempty_directedCutStep_of_follows (follows i)
          (fun same => nonzero i (sub_eq_zero.mpr same.symm)))
      have steps (k : Fin (n + 1)) : E.HistoryProgress L (P.vertex k.castSucc) (P.vertex k.succ) :=
        R.followsStep_progress (R.followsStep_of_common positive disk bound_pos ratio upper (follows k))
      have progress (k : Fin (n + 2)) (earlier : j ≤ k) : E.HistoryProgress L q (P.vertex k) := by
        induction k using Fin.induction with
        | zero =>
          have same : j = 0 := le_antisymm earlier (Fin.zero_le _)
          exact same ▸ SlopeEnvelope.HistoryProgress.refl E q
        | succ k ih =>
          by_cases same : j = k.succ
          · exact same ▸ SlopeEnvelope.HistoryProgress.refl E q
          have earlier' : j ≤ k.castSucc := by
            have ordered : j < k.succ := lt_of_le_of_ne earlier same
            have strict : j.val < k.val + 1 := ordered
            change j.val ≤ k.val
            omega
          exact SlopeEnvelope.HistoryProgress.trans E (ih earlier') (steps k)
      have locate (k : Fin (n + 1)) (before : j.val ≤ k.val) :
          E.HistoryProgress L q (K.projectedVertex (S k).vertex) ∨
            ∃ t ≤ (S k).first, q = (R₀).cutPiecePoint (S k).vertex t := by
        induction k using Fin.induction with
        | zero =>
          have same : j = (0 : Fin (n + 1)).castSucc := Fin.ext (by
            simpa only [Fin.val_zero, Fin.val_castSucc, Nat.le_zero] using before)
          exact Or.inr ⟨(S 0).first, le_rfl, (congrArg P.vertex same).trans (S 0).first_eq⟩
        | succ k ih =>
          let prev := S k.castSucc
          let next := S k.succ
          have join : P.vertex k.castSucc.succ = P.vertex k.succ.castSucc := by
            exact congrArg P.vertex (Fin.ext rfl)
          have next_at : P.vertex k.succ.castSucc = (R₀).cutPiecePoint next.vertex next.first :=
            next.first_eq
          by_cases at_anchor : j.val = k.val + 1
          · have same : j = k.succ.castSucc := Fin.ext at_anchor
            exact Or.inr ⟨next.first, le_rfl, (congrArg P.vertex same).trans next_at⟩
          have earlier' : j.val ≤ k.castSucc.val := by
            change j.val ≤ k.val + 1 at before
            change j.val ≤ k.val
            omega
          by_cases same : prev.vertex = next.vertex
          · have param : prev.last = next.first := (R₀).cutPiecePoint_injective prev.vertex
              (prev.last_eq.symm.trans (join.trans (next_at.trans
                (congrArg (fun v => (R₀).cutPiecePoint v next.first) same.symm))))
            rcases ih earlier' with historic | ⟨t, ht, eq⟩
            · exact Or.inl (same ▸ historic)
            · exact Or.inr ⟨t, ht.trans (prev.ordered.le.trans_eq param), same ▸ eq⟩
          · have first_zero := directedCutSwitch_first_eq_zero compact nonempty R no_boundary
              positive disk bound_pos ratio upper prev next join same
            have equal : P.vertex k.succ.castSucc = K.projectedVertex next.vertex :=
              next_at.trans (by rw [first_zero, (R₀).cutPiecePoint_zero])
            exact Or.inl (equal ▸ progress k.succ.castSucc before)
      let step := S i
      change γ * (‖P.vertex i.castSucc - q‖ * ‖P.vertex i.succ - P.vertex i.castSucc‖) ≤
        inner ℝ (P.vertex i.castSucc - q) (P.vertex i.succ - P.vertex i.castSucc)
      rcases locate i earlier with historic | ⟨t, ht, same⟩
      · apply step.radial_margin_of_carrier
        apply Eq.mpr (congrArg (fun p =>
          γ * (‖p - q‖ * ‖(R₀).cutPieceDirection step.vertex‖) ≤
            inner ℝ (p - q) ((R₀).cutPieceDirection step.vertex)) step.first_eq)
        by_cases root : step.vertex ∈ (R₀).parents.roots
        · let v := (R₀).terminalIndex ⟨step.vertex, root⟩
          have at_root : (R.exterior.point v) = K.projectedVertex step.vertex := R.exterior_points v
          have history : E.HistoryProgress L q (R.exterior.point v) := at_root.symm ▸ historic
          have polar (z : Plane) (hz : z ∈ SlopeEnvelope.historyCone L (R.exterior.slope v)) :
              γ * ‖z‖ ≤ inner ℝ z (R.exterior.direction (R.exterior.slope v)) :=
            (mul_le_mul_of_nonneg_right exterior_margin (norm_nonneg _)).trans (R.exterior_polar v z hz)
          have h := R.exterior.radial_margin_ray boundary v nonnegative small polar history
            step.first_nonneg
          rw [(R₀).cutPiecePoint_terminal ⟨step.vertex, root⟩,
            (R₀).cutPieceDirection_terminal ⟨step.vertex, root⟩]
          change γ * (‖R.exterior.ray v step.first - q‖ *
            ‖R.exterior.direction (R.exterior.slope v)‖) ≤
              inner ℝ (R.exterior.ray v step.first - q) (R.exterior.direction (R.exterior.slope v))
          let radius := ‖R.exterior.ray v step.first - q‖
          have scale : γ * (radius * ‖R.exterior.direction (R.exterior.slope v)‖) =
              γ * radius :=
            (congrArg (fun t => γ * (radius * t)) (R.exterior.unit v)).trans
              (congrArg (γ * ·) (mul_one radius))
          exact scale.le.trans h
        · rw [(R₀).cutPiecePoint_nonroot_add root, (R₀).cutPieceDirection_nonroot root]
          exact R.parent_radial_margin nonnegative small interior_margin exterior_margin root
            historic step.first_nonneg
      · exact step.radial_margin_of_same_piece nonnegative small ht same

end Unfoldings.ConvexRoof
