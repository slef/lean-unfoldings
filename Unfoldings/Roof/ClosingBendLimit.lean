module

public import Unfoldings.Roof.SharpSectionContacts
public import Unfoldings.Geometry.TwoLinkMonotoneChain

/-! A closing bend off the creases has a vanishing one-face error in the chord limit. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The actual bend error vanishes as both directions approach positive
multiples of the same ray. -/
theorem tendsto_closingBend_angleError_of_positive_collinear (f : Face) {a b m : Plane}
    (left_ne : m - a ≠ 0) {t : ℝ} (positive : 0 < t)
    (same : b - m = t • (m - a)) :
    Tendsto (fun c : Plane => |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
      angle (c - a) (b - c)|) (𝓝 m) (𝓝 0) := by
  have right_ne : b - m ≠ 0 := same.symm ▸ smul_ne_zero positive.ne' left_ne
  let left (c : Plane) := c - a
  let right (c : Plane) := b - c
  have left_cont : ContinuousAt left m := continuousAt_id.sub continuousAt_const
  have right_cont : ContinuousAt right m := continuousAt_const.sub continuousAt_id
  have lifted : Continuous (K.sectionDirection f) := by
    rw [show K.sectionDirection f =
      fun d => (K.folding.place f).linear ((K.projectFaceEquiv f).linear.symm d) from
        funext (K.sectionDirection_eq_place_linear f)]
    exact (K.folding.place f).linearIsometry.continuous.comp
      (K.projectFaceEquiv f).linear.symm.continuous_of_finiteDimensional
  have planar_at : ContinuousAt (fun z : Plane × Plane => angle z.1 z.2) (left m, right m) :=
    continuousAt_angle left_ne right_ne
  have spatial_at : ContinuousAt (fun z : Space × Space => angle z.1 z.2)
      (K.sectionDirection f (left m), K.sectionDirection f (right m)) :=
    continuousAt_angle (K.sectionDirection_ne_zero f left_ne) (K.sectionDirection_ne_zero f right_ne)
  have projected_angle : ContinuousAt (fun c => angle (left c) (right c)) m :=
    planar_at.comp (f := fun c : Plane => (left c, right c)) (left_cont.prodMk right_cont)
  have spatial_angle : ContinuousAt (fun c => angle (K.sectionDirection f (left c))
      (K.sectionDirection f (right c))) m :=
    spatial_at.comp
      (f := fun c : Plane => (K.sectionDirection f (left c), K.sectionDirection f (right c)))
      ((lifted.continuousAt.comp left_cont).prodMk (lifted.continuousAt.comp right_cont))
  have zero : |angle (K.sectionDirection f (left m)) (K.sectionDirection f (right m)) -
      angle (left m) (right m)| = 0 := by
    change |angle (K.sectionDirection f (m - a)) (K.sectionDirection f (b - m)) -
      angle (m - a) (b - m)| = 0
    rw [same, K.sectionDirection_smul, angle_smul_right_of_pos _ _ positive,
      angle_smul_right_of_pos _ _ positive, angle_self left_ne,
      angle_self (K.sectionDirection_ne_zero f left_ne), sub_self, abs_zero]
  have limit := (spatial_angle.sub projected_angle).abs.tendsto
  change Tendsto (fun c : Plane => |angle (K.sectionDirection f (left c))
    (K.sectionDirection f (right c)) - angle (left c) (right c)|) (𝓝 m)
    (𝓝 (|angle (K.sectionDirection f (left m)) (K.sectionDirection f (right m)) -
      angle (left m) (right m)|)) at limit
  rwa [zero] at limit

/-- In particular, the two directions agree at the chord midpoint. -/
theorem tendsto_closingBend_angleError (f : Face) {a b : Plane} (different : a ≠ b) :
    Tendsto (fun c : Plane => |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
      angle (c - a) (b - c)|) (𝓝 (midpoint ℝ a b)) (𝓝 0) := by
  let m := midpoint ℝ a b
  have middle : m + m = a + b := midpoint_add_self (R := ℝ) _ _
  have left_ne : m - a ≠ 0 := sub_ne_zero.mpr (fun eq =>
    different ((midpoint_eq_left_iff ℝ).mp eq))
  apply K.tendsto_closingBend_angleError_of_positive_collinear f left_ne (t := 1) zero_lt_one
  rw [one_smul]
  calc
    b - m = a + b - a - m := by abel
    _ = m - a := by rw [← middle]; abel

/-- The bound is uniform over the finitely many possible active support faces. -/
theorem eventually_all_closingBend_angleError_lt {a b : Plane} (different : a ≠ b)
    {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ c in 𝓝 (midpoint ℝ a b), ∀ f : Face,
      |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
        angle (c - a) (b - c)| < ε :=
  Filter.eventually_all.mpr (fun f => (K.tendsto_closingBend_angleError f different).eventually
    (gt_mem_nhds positive))

/-- A regular near-chord connector can make both its direction mismatch
and its one-plane bend error as small as desired on the actual roof. -/
theorem exists_regular_closing_with_small_bend {n : ℕ} (P : PolygonalChain Plane n)
    (nonempty : 0 < n) (progress : ∀ i, 0 < (P.edge i) 0)
    {I J : Type*} [Finite I] [Finite J] (point : I → Plane) (edge : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, edge j ≠ 0) (first : ∀ i, P.vertex 0 ≠ point i)
    (last : ∀ i, P.vertex (Fin.last n) ≠ point i) {U : Set Plane} (opens : IsOpen U)
    (center : midpoint ℝ (P.vertex 0) (P.vertex (Fin.last n)) ∈ U) {ε : ℝ} (positive : 0 < ε) :
    let a := P.vertex 0
    let b := P.vertex (Fin.last n)
    ∃ c ∈ U,
      (∀ i, 0 < ((P.forwardClosingChain c).edge i) 0) ∧
      (∀ j, edge j c ≠ 0) ∧
      (∀ (j : Fin 2) (t : ℝ) i,
        AffineMap.lineMap (P.twoClosingLinks c j).1 (P.twoClosingLinks c j).2 t ≠ point i) ∧
      (Set.range P.path ∩ Set.range (P.forwardClosingChain c).path).Finite ∧
      ‖NormedSpace.normalize (c - a) - NormedSpace.normalize (b - c)‖ < ε ∧
      ∀ f : Face, |angle (K.sectionDirection f (c - a)) (K.sectionDirection f (b - c)) -
        angle (c - a) (b - c)| < ε := by
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have order : x a < x b := P.strictMono_linear_vertices x progress
    (show (0 : Fin (n + 1)) < Fin.last n from nonempty)
  have different : a ≠ b := fun eq => order.ne (congrArg x eq)
  obtain ⟨radius, radius_pos, small_bend⟩ := Metric.eventually_nhds_iff_ball.mp
    (K.eventually_all_closingBend_angleError_lt different positive)
  obtain ⟨c, member, controls, no_edge, no_vertex, finite, mismatch⟩ :=
    P.exists_regular_forwardClosingChain nonempty progress point edge proper first last
      (opens.inter Metric.isOpen_ball) ⟨center, Metric.mem_ball_self radius_pos⟩ positive
  exact ⟨c, member.1, controls, no_edge, no_vertex, finite, mismatch, small_bend c member.2⟩

end Unfoldings.ConvexRoof
