module

public import Unfoldings.Geometry.ChainGraphLenses
public import Unfoldings.Geometry.NearChordClosure
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Near the chord midpoint, both forward closing links converge to the chord heading. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane n)

local notation "a" => P.vertex 0
local notation "b" => P.vertex (Fin.last n)

/-- Follow the two closing segments in the same horizontal order as the bank. -/
def forwardClosingChain (c : Plane) : PolygonalChain Plane 2 :=
  ⟨![a, c, b]⟩

@[simp] theorem forwardClosingChain_start (c : Plane) :
    (P.forwardClosingChain c).vertex 0 = a := rfl

@[simp] theorem forwardClosingChain_end (c : Plane) :
    (P.forwardClosingChain c).vertex (Fin.last 2) = b := rfl

theorem forwardClosingChain_progress (c : Plane) (first : a 0 < c 0) (last : c 0 < b 0) :
    ∀ i, 0 < ((P.forwardClosingChain c).edge i) 0 := by
  intro i
  fin_cases i
  · exact sub_pos.mpr first
  · exact sub_pos.mpr last

theorem forwardClosingChain_trace (c : Plane) :
    Set.range (P.forwardClosingChain c).path = segment ℝ b c ∪ segment ℝ c a := by
  rw [(P.forwardClosingChain c).path_range_eq_segments]
  change {a} ∪ (⋃ i : Fin 2, segment ℝ (![a, c, b] i.castSucc) (![a, c, b] i.succ)) = _
  ext p
  constructor
  · rintro (source | member)
    · exact Or.inr ((Set.mem_singleton_iff.mp source).symm ▸ right_mem_segment ℝ c a)
    · obtain ⟨i, on_link⟩ := Set.mem_iUnion.mp member
      fin_cases i
      · exact Or.inr ((segment_symm ℝ a c) ▸ on_link)
      · exact Or.inl ((segment_symm ℝ c b) ▸ on_link)
  · rintro (on_last | on_first)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨1, (segment_symm ℝ b c) ▸ on_last⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, (segment_symm ℝ c a) ▸ on_first⟩)

/-- The directions of the two forward links coalesce as their bend tends to
the midpoint of the original nonzero chord. -/
theorem tendsto_forwardClosing_directionDifference (different : a ≠ b) :
    Tendsto (fun c : Plane => ‖NormedSpace.normalize (c - a) - NormedSpace.normalize (b - c)‖)
      (𝓝 (midpoint ℝ a b)) (𝓝 0) := by
  let p := midpoint ℝ a b
  have middle : p + p = a + b := midpoint_add_self (R := ℝ) _ _
  have same : p - a = b - p := by
    calc
      p - a = p + p - a - p := by abel
      _ = b - p := by rw [middle]; abel
  have left_ne : p - a ≠ 0 := sub_ne_zero.mpr (fun h =>
    different (((midpoint_eq_left_iff ℝ).mp h)))
  have right_ne : b - p ≠ 0 := same ▸ left_ne
  let v (c : Plane) := c - a
  let w (c : Plane) := b - c
  have left_cont : ContinuousAt v p := continuousAt_id.sub continuousAt_const
  have right_cont : ContinuousAt w p := continuousAt_const.sub continuousAt_id
  have normalize_left : ContinuousAt (fun c => NormedSpace.normalize (v c)) p :=
    (left_cont.norm.inv₀ (norm_ne_zero_iff.mpr left_ne)).smul left_cont
  have normalize_right : ContinuousAt (fun c => NormedSpace.normalize (w c)) p :=
    (right_cont.norm.inv₀ (norm_ne_zero_iff.mpr right_ne)).smul right_cont
  have continuous_order := (normalize_left.sub normalize_right).norm
  have zero : ‖NormedSpace.normalize (v p) - NormedSpace.normalize (w p)‖ = 0 := by
    change ‖NormedSpace.normalize (p - a) - NormedSpace.normalize (b - p)‖ = 0
    rw [same, sub_self, norm_zero]
  exact zero ▸ continuous_order

/-- Construct a regular closing chain with finitely many bank contacts and
an arbitrarily small mismatch between its two forward unit directions. -/
theorem exists_regular_forwardClosingChain (nonempty : 0 < n)
    (progress : ∀ i, 0 < (P.edge i) 0)
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, a ≠ point i) (last : ∀ i, b ≠ point i)
    {U : Set Plane} (opens : IsOpen U) (center : midpoint ℝ a b ∈ U)
    {η : ℝ} (positive : 0 < η) :
    ∃ c ∈ U,
      (∀ i, 0 < ((P.forwardClosingChain c).edge i) 0) ∧
      (∀ j, edge j c ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i) ∧
      (Set.range P.path ∩ Set.range (P.forwardClosingChain c).path).Finite ∧
      ‖NormedSpace.normalize (c - a) - NormedSpace.normalize (b - c)‖ < η := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have ordered : x a < x b := P.strictMono_linear_vertices x progress
    (show (0 : Fin (n + 1)) < Fin.last n from nonempty)
  have distinct : a ≠ b := fun eq => ordered.ne (congrArg x eq)
  have eventual := (P.tendsto_forwardClosing_directionDifference distinct).eventually
    (gt_mem_nhds positive)
  obtain ⟨ε, ε_pos, ball⟩ := Metric.mem_nhds_iff.mp eventual
  obtain ⟨c, hc, start, finish, regular, no_vertices, finite⟩ :=
    P.exists_regular_nearChord_apex x ordered point edge proper first last opens center ε_pos
  refine ⟨c, hc.1, P.forwardClosingChain_progress c start finish, regular, no_vertices, ?_, ball hc.2⟩
  rwa [P.forwardClosingChain_trace c]

end Unfoldings.PolygonalChain
