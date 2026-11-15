module

public import Unfoldings.Metric.PolygonalCut
public import Unfoldings.Metric.PhysicalSeamsLocalExcision

/-! Equal local cut germs give exact whole-ball metric restoration, including cut-bank centers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))

omit [Finite I] in
/-- Closing each attachment separately preserves local equality of the actual cut sets. -/
theorem cutSeams_carrier_iff_of_local_eq (cuts other : Set E) {U : Set E} (open_U : IsOpen U)
    (same : ∀ z ∈ U, z ∈ cuts ↔ z ∈ other) {x : E} (inside : x ∈ U) (i j : I) :
    x ∈ (cutSeams cells closed cuts).carrier i j ↔
      x ∈ (cutSeams cells closed other).carrier i j := by
  have forward (C D : Set E) (agree : ∀ z ∈ U, z ∈ C ↔ z ∈ D)
      (member : x ∈ closure ((cells i ∩ cells j) \ C)) :
      x ∈ closure ((cells i ∩ cells j) \ D) := by
    have restricted := open_U.inter_closure ⟨inside, member⟩
    apply closure_mono ?_ restricted
    intro z hz
    exact ⟨hz.2.1, fun cut => hz.2.2 ((agree z hz.1).mpr cut)⟩
  exact ⟨forward cuts other same, forward other cuts (fun z hz => (same z hz).symm)⟩

/-- Restoring only cut pieces outside an open neighborhood preserves a whole metric ball.
The center may lie on the retained cut and may have several distinct bank copies. -/
theorem exists_cutRestoreChart_of_local_eq (cuts other : Set E) (included : other ⊆ cuts)
    (a : Total (fun i => cells i)) {ε : ℝ} (positive : 0 < ε)
    (same : ∀ z, dist z a.2.val < ε → (z ∈ cuts ↔ z ∈ other)) :
    Nonempty (ForgetChart (fun i => cells i)
      (cutSeams_relation_mono cells closed cuts included) a) := by
  let S := cutSeams cells closed cuts
  let T := cutSeams cells closed other
  have carrier_inclusion : ∀ i j, S.carrier i j ⊆ T.carrier i j := by
    intro i j
    exact closure_mono (Set.sdiff_subset_sdiff_right included)
  have local_agreement : ∀ i j z, dist z a.2.val < ε → z ∈ T.carrier i j → z ∈ S.carrier i j := by
    intro i j z near member
    exact (cutSeams_carrier_iff_of_local_eq cells closed cuts other Metric.isOpen_ball
      (fun z hz => same z hz) near i j).mpr member
  exact S.exists_forgetChart_of_local_carriers T carrier_inclusion a positive local_agreement

end Unfoldings.MetricGluing
