module

public import Unfoldings.Roof.TruncatedWholeCarrier
public import Unfoldings.Convex.ExteriorBankSupports

/-! Between two truncation levels the original outer cut consists of finite terminal segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- The whole original ray maps each closed parameter interval to its literal segment. -/
theorem terminal_ray_interval (r : {v // v ∈ R.parents.roots}) (s t : ℝ) (ordered : s ≤ t) :
    (fun u : ℝ => R.exterior.ray (R.terminalIndex r) u) '' Set.Icc s t =
      segment ℝ (R.exterior.ray (R.terminalIndex r) s)
        (R.exterior.ray (R.terminalIndex r) t) := by
  let index := R.terminalIndex r
  let line : ℝ →ᵃ[ℝ] Plane :=
    AffineMap.lineMap (R.exterior.point index) (R.exterior.ray index 1)
  have expression : (fun u : ℝ => R.exterior.ray index u) = line :=
    funext (fun u => (R.exterior.ray_lineMap index u).symm)
  calc
    _ = line '' segment ℝ s t := by rw [expression, segment_eq_Icc ordered]
    _ = _ := by
      simpa only [line, R.exterior.ray_lineMap] using image_segment ℝ line s t

variable (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

/-- Original terminal time strictly increases with the geometric truncation level. -/
theorem terminalTime_strictMono (r : {v // v ∈ R.parents.roots}) :
    StrictMono (fun height : ℝ => R.terminalTime height r) := by
  intro first last ordered
  unfold terminalTime
  exact div_lt_div_of_pos_right (sub_lt_sub_right ordered _) (R.exterior.positive _)

include higher in
/-- The original terminal parameter orders the entire outer tail by actual roof height. -/
theorem terminal_ray_superlevel_iff (r : {v // v ∈ R.parents.roots}) {t : ℝ}
    (nonnegative : 0 ≤ t) :
    level ≤ G.height (R.exterior.ray (R.terminalIndex r) t) ↔
      R.terminalTime level r ≤ t := by
  have at_time := R.terminalPoint_level level higher r
  change G.height (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) = level at at_time
  rw [R.exterior.height_ray _ (R.terminalTime_pos level higher r).le] at at_time
  rw [R.exterior.height_ray _ nonnegative]
  have rate : 0 < R.exterior.rate (R.terminalIndex r) :=
    R.exterior.positive (R.terminalIndex r)
  constructor <;> intro bound <;> nlinarith

include higher in
/-- Increasing the geometric truncation level never shortens an original terminal bank. -/
theorem terminalTime_mono {later : ℝ} (ordered : level ≤ later)
    (r : {v // v ∈ R.parents.roots}) :
    R.terminalTime level r ≤ R.terminalTime later r := by
  have later_higher : ∀ v, G.height (K.projectedVertex v) < later :=
    fun v => (higher v).trans_le ordered
  apply (R.terminal_ray_sublevel_iff later later_higher r
    (R.terminalTime_pos level higher r).le).mp
  exact (R.terminalPoint_level level higher r).le.trans ordered

include higher in
/-- All cuts above the old level and below a later level are exactly the original terminal
segments between their two named truncation endpoints. No parent segment occurs in this band. -/
theorem carrier_inter_closed_band {later : ℝ} (ordered : level ≤ later) :
    R.carrier ∩ {p | level ≤ G.height p ∧ G.height p ≤ later} =
      ⋃ r : {v // v ∈ R.parents.roots},
        segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
  have later_higher : ∀ v, G.height (K.projectedVertex v) < later :=
    fun v => (higher v).trans_le ordered
  have strict_sublevel : Convex ℝ {p | G.height p < level} := by
    simpa only [Set.mem_univ, true_and] using G.convex_height.convex_lt level
  apply Set.Subset.antisymm
  · rintro p ⟨finite | infinite, above, below⟩
    · obtain ⟨edge, member⟩ := Set.mem_iUnion.mp finite
      exact (not_lt_of_ge above (strict_sublevel.segment_subset
        (higher edge.val) (higher (R.parents.parent edge.val)) member)).elim
    · obtain ⟨r, t, nonnegative, position⟩ := Set.mem_iUnion.mp infinite
      refine Set.mem_iUnion.mpr ⟨r, ?_⟩
      change p ∈ segment ℝ (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r))
        (R.exterior.ray (R.terminalIndex r) (R.terminalTime later r))
      rw [← R.terminal_ray_interval r _ _ (R.terminalTime_mono level higher ordered r)]
      refine ⟨t, ⟨?_, ?_⟩, position.symm⟩
      · apply (R.terminal_ray_superlevel_iff level higher r nonnegative).mp
        exact position ▸ above
      · apply (R.terminal_ray_sublevel_iff later later_higher r nonnegative).mp
        exact position ▸ below
  · intro p member
    obtain ⟨r, on_segment⟩ := Set.mem_iUnion.mp member
    change p ∈ segment ℝ (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r))
      (R.exterior.ray (R.terminalIndex r) (R.terminalTime later r)) at on_segment
    rw [← R.terminal_ray_interval r _ _ (R.terminalTime_mono level higher ordered r)] at on_segment
    obtain ⟨t, bounds, rfl⟩ := on_segment
    have nonnegative : 0 ≤ t := (R.terminalTime_pos level higher r).le.trans bounds.1
    exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨r, t, nonnegative, rfl⟩),
      (R.terminal_ray_superlevel_iff level higher r nonnegative).mpr bounds.1,
      (R.terminal_ray_sublevel_iff later later_higher r nonnegative).mpr bounds.2⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
