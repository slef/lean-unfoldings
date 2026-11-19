module

public import Unfoldings.Metric.LocalSeams
public import Unfoldings.Metric.BallFromLocalSteps
public import Unfoldings.Metric.ConvexCover
public import Unfoldings.Metric.BallChart

/-! A finite cover by consistently placed incident cells fills a whole intrinsic metric ball. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I V : Type*} [Finite I] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (cells : I → Set V) (S : ClosedSeams (fun i => cells i)) (a : Total (fun i => cells i))
  (finite : ∀ i, (classIn (fun i => cells i) S.relation a i).Finite)
  (closed : ∀ i, IsClosed (cells i)) (place : ∀ i, cells i → V)
  (rigid : ∀ i, Isometry (place i))

local notation "E" => (fun i => cells i)
local notation "C" => classIn E S.relation a
local notation "Center" => place (Sigma.fst a) (Sigma.snd a)
local notation "Realize" => point E (ClosedSeams.relation S)

include finite closed rigid

/-- Incident cell placements give a whole planar ball once their images fill a ball
and each shared local point represents one quotient point. Cells may be unbounded. -/
theorem hasMetricBallChart_of_placed_cells
    (compatible : ∀ s, S.Incident a s → ∀ x, place (S.left s) (S.toLeft s x) =
      place (S.right s) (S.toRight s x))
    {R : ℝ} (positive : 0 < R)
    (cover : ∀ z ∈ Metric.ball Center R, ∃ (i : I) (p : cells i), (C i).Nonempty ∧ place i p = z)
    (shared : ∀ i j (p : cells i) (q : cells j),
      (C i).Nonempty → (C j).Nonempty → place i p ∈ Metric.ball Center R →
      place i p = place j q → Realize ⟨i, p⟩ = Realize ⟨j, q⟩) :
    HasMetricBallChart V (Realize a) := by
  classical
  obtain ⟨δ, δpos, step⟩ := S.exists_radius_local_step a finite place
    (fun i => (rigid i).lipschitzWith) compatible
  obtain ⟨ε, εpos, transport⟩ := S.class_transport a finite
  let r := min R (min ε (δ / 4))
  have rpos : 0 < r := lt_min positive (lt_min εpos (by positivity))
  have small : r ≤ R := min_le_left _ _
  have metric_small : r ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have step_small : 4 * r ≤ δ := by
    have bound : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let Ball := Metric.ball Center r
  have covered (z : Ball) : ∃ (i : I) (p : cells i), (C i).Nonempty ∧ place i p = z.val :=
    cover z.val (Metric.ball_subset_ball small z.property)
  choose i p active placed using covered
  let fill (z : Ball) := Realize ⟨i z, p z⟩
  have at_patch (z : Ball) (j : I) (q : cells j)
      (present : (C j).Nonempty) (at_z : place j q = z.val) :
      fill z = Realize ⟨j, q⟩ :=
    shared (i z) j (p z) q (active z) present
      ((placed z).symm ▸ Metric.ball_subset_ball small z.property)
      ((placed z).trans at_z.symm)
  let patches (j : {j : I // (C j).Nonempty}) : Set Ball :=
    Subtype.val ⁻¹' Set.range (place j.val)
  have patch_closed (j : {j : I // (C j).Nonempty}) : IsClosed (patches j) := by
    let _ : CompleteSpace (cells j.val) := (closed j.val).isComplete.completeSpace_coe
    exact (rigid j.val).isClosedEmbedding.isClosed_range.preimage continuous_subtype_val
  have patch_cover : ⋃ j, patches j = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Set.mem_iUnion.mpr ⟨⟨i z, active z⟩, p z, placed z⟩
  have patch_lipschitz (j : {j : I // (C j).Nonempty}) :
      LipschitzOnWith 1 fill (patches j) := by
    intro z hz w hw
    obtain ⟨q, at_z⟩ := hz
    obtain ⟨s, at_w⟩ := hw
    rw [at_patch z j.val q j.property at_z, at_patch w j.val s j.property at_w]
    rw [ENNReal.coe_one, one_mul, Subtype.edist_eq, ← at_z, ← at_w]
    exact (edist_of_le E S.relation j.val _ _).trans_eq ((rigid j.val).edist_eq _ _).symm
  have lipschitz := convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    (Metric.ball Center r) (convex_ball _ _) patches patch_closed patch_cover fill 1 patch_lipschitz
  have fills_center : fill ⟨Center, Metric.mem_ball_self rpos⟩ = Realize a := by
    exact at_patch _ a.1 a.2 ⟨a.2, Relation.EqvGen.refl _⟩ rfl
  have reps (z : Ball) : ∃ b, Realize b = fill z ∧ place b.1 b.2 = z.val :=
    ⟨⟨i z, p z⟩, rfl, placed z⟩
  have covers_ball (x : Realization E S.relation)
      (hx : x ∈ Metric.eball (Realize a) (ENNReal.ofReal r)) : ∃ z, fill z = x := by
    obtain ⟨b, rfl⟩ := point_surjective E S.relation x
    have near_root : edist (Realize a) (Realize b) < ENNReal.ofReal r :=
      (edist_comm _ _).trans_lt hx
    obtain ⟨q, hq, near⟩ := exists_classPoint_of_edist_lt E S.relation a εpos metric_small
      finite transport b near_root
    have hc : place b.1 q = Center :=
      (S.class_eq_of_incident_compatible a place compatible hq).symm
    have in_ball : place b.1 b.2 ∈ Metric.ball Center r := by
      rw [Metric.mem_ball, ← hc, (rigid b.1).dist_eq]
      exact near
    exact ⟨⟨place b.1 b.2, in_ball⟩, at_patch _ b.1 b.2 ⟨q, hq⟩ rfl⟩
  obtain ⟨A, _⟩ := ball_isometry_of_local_steps E S.relation a Center rpos
    (fun b => place b.1 b.2)
    (fun b c hb hc => step b c (hb.trans_le (ENNReal.ofReal_le_ofReal step_small))
      (hc.trans_le (ENNReal.ofReal_le_ofReal step_small)))
    fill lipschitz fills_center reps covers_ball
  exact ⟨r, rpos, Center, ⟨A.symm⟩⟩

end Unfoldings.MetricGluing.ClosedSeams
