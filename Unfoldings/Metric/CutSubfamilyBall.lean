module

public import Unfoldings.Metric.CutSubfamilyLocalInverse

/-! Keeping actual incident cells preserves a whole intrinsic ball, without global convexity. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E) (selected : I → Prop)

/-- An actual cut subfamily containing every incident cell preserves a whole original
metric ball. The subfamily need not embed globally isometrically or be convex. -/
theorem exists_cutSubfamily_ball_chart
    (a : Total (fun i : {i // selected i} => cells i.val))
    (incident_selected : ∀ i,
      (classIn (fun i => cells i) (cutSeams cells closed cuts).relation ⟨a.1.val, a.2⟩ i).Nonempty →
        selected i) :
    ∃ r : ℝ, 0 < r ∧
      ∃ B : Metric.eball
        (point (fun i : {i // selected i} => cells i.val)
          (cutSeams (fun i : {i // selected i} => cells i.val)
            (fun i => closed i.val) cuts).relation a)
          (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (point (fun i => cells i) (cutSeams cells closed cuts).relation ⟨a.1.val, a.2⟩)
          (ENNReal.ofReal r),
        ∀ z, (B z).val = cutSubfamilyMap cells closed cuts selected z.val := by
  let S := cutSeams cells closed cuts
  let T := cutSeams (fun i : {i // selected i} => cells i.val) (fun i => closed i.val) cuts
  let root : Total (fun i => cells i) := ⟨a.1.val, a.2⟩
  let source := point (fun i : {i // selected i} => cells i.val) T.relation a
  let F := cutSubfamilyMap cells closed cuts selected
  let f := cutSubfamilyCellMap cells closed cuts selected source
  have finite : ∀ i, (classIn (fun i => cells i) S.relation root i).Finite :=
    fun i => (S.classIn_subsingleton root i).finite
  obtain ⟨δ, δpos, lower⟩ := S.closedSeams.exists_radius_map_edist_le root finite f
    (cutSubfamilyCellMap_lipschitz cells closed cuts selected source)
    (cutSubfamilyCellMap_incident_compatible cells closed cuts
      selected root source incident_selected)
  obtain ⟨ε, εpos, transport⟩ := S.closedSeams.class_transport root finite
  let radius := min δ ε
  have positive : 0 < radius := lt_min δpos εpos
  have F_bound : LipschitzWith 1 F := cutSubfamilyMap_lipschitz cells closed cuts selected
  have center : F source = point (fun i => cells i) S.relation root := rfl
  have source_value (b : Total (fun i : {i // selected i} => cells i.val)) :
      f b.1.val b.2 = point (fun i : {i // selected i} => cells i.val) T.relation b :=
    cutSubfamilyCellMap_of_selected cells closed cuts selected source b.1.val b.1.property b.2
  let map : Metric.eball source (ENNReal.ofReal radius) →
      Metric.eball (point (fun i => cells i) S.relation root) (ENNReal.ofReal radius) := fun z =>
    ⟨F z.val, by
      have bound := F_bound z.val source
      simp only [ENNReal.coe_one, one_mul] at bound
      exact (bound.trans_lt z.property : edist (F z.val) (F source) < ENNReal.ofReal radius)⟩
  have isometric_map : Isometry map := by
    intro z w
    change edist (F z.val) (F w.val) = edist z.val w.val
    apply le_antisymm
    · exact (F_bound z.val w.val).trans_eq (one_mul _)
    · obtain ⟨b, represents_b⟩ := point_surjective
        (fun i : {i // selected i} => cells i.val) T.relation z.val
      obtain ⟨c, represents_c⟩ := point_surjective
        (fun i : {i // selected i} => cells i.val) T.relation w.val
      have point_b : point (fun i => cells i) S.relation ⟨b.1.val, b.2⟩ = F z.val :=
        congrArg F represents_b
      have point_c : point (fun i => cells i) S.relation ⟨c.1.val, c.2⟩ = F w.val :=
        congrArg F represents_c
      have near_b : edist (point (fun i => cells i) S.relation root)
          (point (fun i => cells i) S.relation ⟨b.1.val, b.2⟩) < ENNReal.ofReal δ := by
        rw [point_b, edist_comm]
        exact (map z).property.trans_le (ENNReal.ofReal_le_ofReal (min_le_left δ ε))
      have near_c : edist (point (fun i => cells i) S.relation root)
          (point (fun i => cells i) S.relation ⟨c.1.val, c.2⟩) < ENNReal.ofReal δ := by
        rw [point_c, edist_comm]
        exact (map w).property.trans_le (ENNReal.ofReal_le_ofReal (min_le_left δ ε))
      have bounded := lower ⟨b.1.val, b.2⟩ ⟨c.1.val, c.2⟩ near_b near_c
      have f_b : f b.1.val b.2 = z.val := (source_value b).trans represents_b
      have f_c : f c.1.val c.2 = w.val := (source_value c).trans represents_c
      exact (congrArg₂ edist f_b f_c).symm.trans_le
        (bounded.trans_eq (congrArg₂ edist point_b point_c))
  have onto : Function.Surjective map := by
    intro y
    obtain ⟨b, represents⟩ := point_surjective (fun i => cells i) S.relation y.val
    have near : edist (point (fun i => cells i) S.relation root)
        (point (fun i => cells i) S.relation b) < ENNReal.ofReal radius := by
      rw [represents, edist_comm]
      exact y.property
    obtain ⟨q, related, _⟩ := exists_classPoint_of_edist_lt (fun i => cells i) S.relation root
      εpos (min_le_right δ ε) finite transport b near
    have chosen : selected b.1 := incident_selected b.1 ⟨q, related⟩
    let source_b := of (fun i : {i // selected i} => cells i.val) T.relation ⟨b.1, chosen⟩ b.2
    have f_b : f b.1 b.2 = source_b :=
      cutSubfamilyCellMap_of_selected cells closed cuts selected source b.1 chosen b.2
    have f_root : f root.1 root.2 = source := source_value a
    have root_near : edist (point (fun i => cells i) S.relation root)
        (point (fun i => cells i) S.relation root) < ENNReal.ofReal δ := by
      rw [edist_self]
      exact ENNReal.ofReal_pos.mpr δpos
    have bounded := lower b root
      (near.trans_le (ENNReal.ofReal_le_ofReal (min_le_left δ ε))) root_near
    have source_near : edist source_b source < ENNReal.ofReal radius :=
      ((congrArg₂ edist f_b f_root).symm.trans_le bounded).trans_lt (by
        rwa [edist_comm])
    refine ⟨⟨source_b, source_near⟩, ?_⟩
    exact Subtype.ext represents
  exact ⟨radius, positive, ⟨Equiv.ofBijective map ⟨isometric_map.injective, onto⟩, isometric_map⟩,
    fun _ => rfl⟩

/-- A purely physical neighborhood criterion supplies all incident-cell membership.
All cut copies at the center are retained, with no class or local metric certificate. -/
theorem exists_cutSubfamily_ball_chart_of_cells_at_point
    (a : Total (fun i : {i // selected i} => cells i.val))
    (selected_at_point : ∀ i, a.2.val ∈ cells i → selected i) :
    ∃ r : ℝ, 0 < r ∧
      ∃ B : Metric.eball
        (point (fun i : {i // selected i} => cells i.val)
          (cutSeams (fun i : {i // selected i} => cells i.val)
            (fun i => closed i.val) cuts).relation a)
          (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (point (fun i => cells i) (cutSeams cells closed cuts).relation ⟨a.1.val, a.2⟩)
          (ENNReal.ofReal r),
        ∀ z, (B z).val = cutSubfamilyMap cells closed cuts selected z.val := by
  apply exists_cutSubfamily_ball_chart cells closed cuts selected a
  rintro i ⟨p, related⟩
  apply selected_at_point i
  have physical := (cutSeams cells closed cuts).physical_eq_of_eqvGen related
  exact Eq.mpr (congrArg (fun z : E => z ∈ cells i) physical) p.property

end Unfoldings.MetricGluing
