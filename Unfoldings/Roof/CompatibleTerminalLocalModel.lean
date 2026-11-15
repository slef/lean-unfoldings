module

public import Unfoldings.Roof.CompatibleWholeCutModel
public import Unfoldings.Roof.CompatibleTerminalCutGerm
public import Unfoldings.Convex.ExteriorRayFaceGerms

/-! One actual complete cut model carries both terminal support faces and the isolated cut line. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- The original cut equation is the exact supporting line of the actual exterior ray. -/
theorem terminal_exterior_equation (r : {v // v ∈ R.parents.roots}) :
    orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val) =
      orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1) := by
  have source : R.exterior.point (R.terminalIndex r) = K.projectedVertex r.val :=
    R.exterior_points _
  have last : R.exterior.ray (R.terminalIndex r) 1 = R.wholeCutLast r.val := by
    rw [← R.terminal_lineMap r 1, AffineMap.lineMap_apply_one]
  rw [source, last]

namespace WholeCutModel

variable {R} {M : G.FiniteSlopeModel} (W : R.WholeCutModel M)

/-- Two fixed actual cells of this same retained partition provide both whole tail copies
and the exact original roof faces at every positive point of the ray. -/
theorem terminal_roof_face_germs (r : {v // v ∈ R.parents.roots}) :
    ∃ l b : W.Index, W.terminalSigns r l = true ∧ W.terminalSigns r b = false ∧
      ∃ T : ℝ, 0 < T ∧
        (∀ t : ℝ, T ≤ t → R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint l ∧
          R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint b) ∧
        (∀ t : ℝ, 0 ≤ t →
          SpatialEnvelope.height M.plane (R.exterior.ray (R.terminalIndex r) t) =
            (M.plane (W.partition.support l)).height (R.exterior.ray (R.terminalIndex r) t) ∧
          SpatialEnvelope.height M.plane (R.exterior.ray (R.terminalIndex r) t) =
            (M.plane (W.partition.support b)).height (R.exterior.ray (R.terminalIndex r) t)) ∧
        ∀ t : ℝ, 0 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ z,
          dist z (R.exterior.ray (R.terminalIndex r) t) < δ →
          (0 ≤ orient (R.exterior.point (R.terminalIndex r))
              (R.exterior.ray (R.terminalIndex r) 1) z →
            SpatialEnvelope.height M.plane z = (M.plane (W.partition.support l)).height z) ∧
          (orient (R.exterior.point (R.terminalIndex r))
              (R.exterior.ray (R.terminalIndex r) 1) z ≤ 0 →
            SpatialEnvelope.height M.plane z = (M.plane (W.partition.support b)).height z) := by
  apply R.exterior.exists_whole_ray_two_face_germs M W.partition (R.terminalIndex r)
    (W.terminalSigns r)
  intro c x hx
  have lower := W.terminal_aligned r c x hx
  rwa [R.terminal_exterior_equation r] at lower

end WholeCutModel
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

include no_boundary in
/-- Construct the exact two-face, single-cut local geometry in this actual complete cut model.
All positive terminal points are covered; local fan metric charts are a subsequent step. -/
theorem exists_terminal_local_model (r : {v // v ∈ R.parents.roots}) :
    ∃ l b : W.Index, W.terminalSigns r l = true ∧ W.terminalSigns r b = false ∧
      ∃ T : ℝ, 0 < T ∧
        (∀ t : ℝ, T ≤ t → R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint l ∧
          R.exterior.ray (R.terminalIndex r) t ∈ W.partition.footprint b) ∧
        ∀ t : ℝ, 0 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ z,
          dist z (R.exterior.ray (R.terminalIndex r) t) < δ →
          (z ∈ R.carrier ↔ orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val) z = 0) ∧
          (0 ≤ orient (K.projectedVertex r.val) (R.wholeCutLast r.val) z →
            SpatialEnvelope.height M.plane z = (M.plane (W.partition.support l)).height z) ∧
          (orient (K.projectedVertex r.val) (R.wholeCutLast r.val) z ≤ 0 →
            SpatialEnvelope.height M.plane z = (M.plane (W.partition.support b)).height z) := by
  obtain ⟨l, b, hl, hb, T, positive, tail, _active, roof⟩ := W.terminal_roof_face_germs r
  refine ⟨l, b, hl, hb, T, positive, tail, ?_⟩
  intro t ht
  obtain ⟨δ, δpos, cut⟩ := K.exists_terminal_cut_line_germ compact nonempty R no_boundary r ht
  obtain ⟨ε, εpos, geometry⟩ := roof t ht
  refine ⟨min δ ε, lt_min δpos εpos, ?_⟩
  intro z near
  have same_orient : orient (K.projectedVertex r.val) (R.wholeCutLast r.val) z =
      orient (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1) z := by
    simpa only [orientMap_apply] using
      congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f z) (R.terminal_exterior_equation r)
  have sides := geometry z (near.trans_le (min_le_right δ ε))
  rw [← same_orient] at sides
  exact ⟨cut z (near.trans_le (min_le_left δ ε)), sides⟩

end Unfoldings.ConvexRoof
