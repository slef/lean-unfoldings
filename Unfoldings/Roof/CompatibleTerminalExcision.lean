module

public import Unfoldings.Roof.CompatibleTerminalLocalModel
public import Unfoldings.Geometry.SpatialEnvelopeCutExcision

/-! Restoring other forest cuts preserves whole balls at each positive terminal bank copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- Keep the entire original terminal ray while restoring every other forest cut. -/
def terminalRayCut (r : {v // v ∈ R.parents.roots}) : Set Plane :=
  MetricGluing.rayCut (K.projectedVertex r.val) (R.wholeCutLast r.val)

theorem terminalRayCut_subset_carrier (r : {v // v ∈ R.parents.roots}) :
    R.terminalRayCut r ⊆ R.carrier := by
  rw [R.carrier_eq_iUnion_closedPiece]
  intro x member
  exact Set.mem_iUnion.mpr ⟨r.val, (R.closedPiece_root r).symm ▸ member⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance terminalExcisionIndexFintype : Fintype W.Index := W.finiteIndex

include no_boundary in
/-- The full forest and this actual terminal ray have exactly the same geometric cut germ. -/
theorem exists_terminalRayCut_germ (r : {v // v ∈ R.parents.roots}) {t : ℝ}
    (positive : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z (R.exterior.ray (R.terminalIndex r) t) < ε →
      (z ∈ R.carrier ↔ z ∈ R.terminalRayCut r) := by
  obtain ⟨δ, δpos, cut⟩ := K.exists_terminal_cut_line_germ compact nonempty R no_boundary r positive
  have forward : R.exterior.ray (R.terminalIndex r) t ∈
      rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val) := by
    rw [← R.terminal_lineMap r t]
    exact lineMap_mem_rayForwardHalfspace (R.terminal_endpoints_ne r) positive
  obtain ⟨ε, εpos, near_forward⟩ := Metric.isOpen_iff.mp
    (isOpen_rayForwardHalfspace (K.projectedVertex r.val) (R.wholeCutLast r.val)) _ forward
  refine ⟨min δ ε, lt_min δpos εpos, ?_⟩
  intro z near
  constructor
  · intro member
    have zero := (cut z (near.trans_le (min_le_left δ ε))).mp member
    have on_forward := near_forward (Metric.mem_ball.mpr (near.trans_le (min_le_right δ ε)))
    obtain ⟨s, spos, expression⟩ := exists_positive_ray_parameter
      (R.terminal_endpoints_ne r) on_forward zero
    exact ⟨⟨s, spos.le⟩, expression.symm⟩
  · intro member
    exact R.terminalRayCut_subset_carrier r member

include no_boundary in
/-- A whole intrinsic ball about each positive terminal bank copy survives restoration
of all the other forest cuts. The exact canonical map and the physical roof are preserved. -/
theorem exists_terminalRayCut_ball_chart (r : {v // v ∈ R.parents.roots}) {t : ℝ}
    (positive : 0 < t) (x : W.Cut)
    (position : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
      R.exterior.ray (R.terminalIndex r) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : Metric.eball x (ENNReal.ofReal ε) ≃ᵢ
      Metric.eball (W.partition.forgetCut R.carrier (R.terminalRayCut r)
        (R.terminalRayCut_subset_carrier r) x) (ENNReal.ofReal ε),
      ∀ y, (B y).val = W.partition.forgetCut R.carrier (R.terminalRayCut r)
        (R.terminalRayCut_subset_carrier r) y.val := by
  obtain ⟨a, represents⟩ := MetricGluing.point_surjective (fun a => W.partition.planarCell a)
    (W.partition.cutGlue R.carrier) x
  have horizontal : Cap.horizontal ((M.plane (W.partition.support a.1)).place a.2.val) =
      R.exterior.ray (R.terminalIndex r) t := by
    rw [← represents] at position
    exact position
  obtain ⟨δ, δpos, same⟩ := K.exists_terminalRayCut_germ compact nonempty R no_boundary r positive
  obtain ⟨chart⟩ := W.partition.exists_forgetCut_ball_chart R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r) a δpos (by simpa only [horizontal] using same)
  have result : ∃ ε : ℝ, 0 < ε ∧ ∃ B :
      Metric.eball (MetricGluing.point (fun a => W.partition.planarCell a)
        (W.partition.cutGlue R.carrier) a) (ENNReal.ofReal ε) ≃ᵢ
      Metric.eball (W.partition.forgetCut R.carrier (R.terminalRayCut r)
        (R.terminalRayCut_subset_carrier r) (MetricGluing.point (fun a => W.partition.planarCell a)
          (W.partition.cutGlue R.carrier) a)) (ENNReal.ofReal ε),
        ∀ y, (B y).val = W.partition.forgetCut R.carrier (R.terminalRayCut r)
          (R.terminalRayCut_subset_carrier r) y.val :=
    ⟨chart.radius, chart.positive, chart.chart, chart.agrees⟩
  rwa [represents] at result

end Unfoldings.ConvexRoof
