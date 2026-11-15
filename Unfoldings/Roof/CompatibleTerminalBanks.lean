module

public import Unfoldings.Roof.CompatibleWholeCutPartition
public import Unfoldings.Geometry.SpatialEnvelopeRayBanks

/-! Actual compatible one-ended forest cuts have two disjoint, exact, unbounded terminal banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem terminal_lineMap (r : {v // v ∈ R.parents.roots}) (t : ℝ) :
    AffineMap.lineMap (K.projectedVertex r.val) (R.wholeCutLast r.val) t =
      R.exterior.ray (R.terminalIndex r) t := by
  classical
  simp only [wholeCutLast, dite_eq_left r.property, SlopeEnvelope.ExteriorPlan.ray,
    R.exterior_points, AffineMap.lineMap_apply_module', add_sub_cancel_left]
  exact add_comm _ _

theorem terminal_endpoints_ne (r : {v // v ∈ R.parents.roots}) :
    K.projectedVertex r.val ≠ R.wholeCutLast r.val := by
  classical
  intro equal
  have offset := congrArg (fun z => z - K.projectedVertex r.val) equal
  simp only [wholeCutLast, dite_eq_left r.property, sub_self, add_sub_cancel_left] at offset
  have unit := R.exterior.unit (R.terminalIndex r)
  rw [← offset, norm_zero] at unit
  norm_num at unit

theorem terminal_orient_equation (r : {v // v ∈ R.parents.roots}) :
    R.wholeCutEquation ((Fintype.equivFin (C.Vertex Set.univ)) r.val) =
      orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val) := by
  classical
  simp only [wholeCutEquation, Equiv.symm_apply_apply, segmentEquation,
    ite_eq_right (R.terminal_endpoints_ne r)]

/-- Construct the full compatible cut metric and both actual banks of each terminal ray.
The banks are disjoint in the metric quotient, fold to the original whole ray, and
preserve every pairwise spatial distance. Their tails have no upper truncation. -/
theorem exists_whole_cut_partition_with_ray_banks (M : G.FiniteSlopeModel) :
    ∃ (A : Type) (_ : Fintype A) (P : SpatialEnvelope.WholePartition M.plane A),
      R.carrier ⊆ ⋃ a, frontier (P.footprint a) ∧ CompleteSpace (P.Cut R.carrier) ∧
      Function.Surjective (P.restoreCut R.carrier) ∧
      ∀ r : {v // v ∈ R.parents.roots}, ∃ T : ℝ, 0 < T ∧
        ∃ L B : Set.Ici T → P.Cut R.carrier,
          (∀ t, (P.restoreCut R.carrier (L t)).val =
              SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) ∧
            (P.restoreCut R.carrier (B t)).val =
              SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val)) ∧
          (∀ s t, edist (L s) (L t) =
            edist (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) s.val))
              (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val))) ∧
          (∀ s t, edist (B s) (B t) =
            edist (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) s.val))
              (SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val))) ∧
          Disjoint (Set.range L) (Set.range B) := by
  obtain ⟨A, inst, P, signs, constrained⟩ := SpatialEnvelope.exists_wholePartition M.plane
    R.wholeCutEquation R.wholeCutEquation_ne_zero
  let : Fintype A := inst
  refine ⟨A, inst, P, ?_, P.cut_complete R.carrier, P.restoreCut_surjective R.carrier, ?_⟩
  · intro x member
    obtain ⟨i, zero⟩ := R.carrier_covered_by_wholeCutEquations x member
    have covered : x ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp covered
    exact Set.mem_iUnion.mpr ⟨a, P.mem_frontier_of_constraint R.wholeCutEquation
      R.wholeCutEquation_ne_zero signs constrained a ha i zero⟩
  · intro r
    have aligned : ∀ c x, x ∈ P.footprint c →
        0 ≤ AffineArrangement.signed
          (orientMap (K.projectedVertex r.val) (R.wholeCutLast r.val))
          (signs c ((Fintype.equivFin (C.Vertex Set.univ)) r.val)) x := by
      intro c x hx
      have lower := constrained c x hx ((Fintype.equivFin (C.Vertex Set.univ)) r.val)
      rwa [R.terminal_orient_equation r] at lower
    have cut_ray : ∀ t : ℝ, 0 ≤ t →
        AffineMap.lineMap (K.projectedVertex r.val) (R.wholeCutLast r.val) t ∈ R.carrier := by
      intro t nonnegative
      exact Or.inr (Set.mem_iUnion.mpr ⟨r, t, nonnegative, R.terminal_lineMap r t⟩)
    simpa only [R.terminal_lineMap] using P.exists_unbounded_ray_banks R.carrier
      (K.projectedVertex r.val) (R.wholeCutLast r.val) (R.terminal_endpoints_ne r)
      cut_ray (fun c => signs c ((Fintype.equivFin (C.Vertex Set.univ)) r.val)) aligned

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
