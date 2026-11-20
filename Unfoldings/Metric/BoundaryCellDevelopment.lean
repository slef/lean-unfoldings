module

public import Unfoldings.Geometry.ConvexInteriorRigidity
public import Unfoldings.Metric.Local
public import Unfoldings.Metric.Connected

/-! Local planar developments are rigid on each convex cell of a boundary-only gluing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u

variable {I : Type u} (cells : I → Set Plane)
  (glue : Total (fun i => cells i) → Total (fun i => cells i) → Prop)
  [PreconnectedSpace (Realization (fun i => cells i) glue)]

local instance boundaryCellDevelopmentMetricSpace :
    MetricSpace (Realization (fun i => cells i) glue) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

variable (f : Realization (fun i => cells i) glue → Plane) (continuous_f : Continuous f)
  (local_isometry : ∀ x, ∃ r > 0, Isometry (fun y : Metric.ball x r => f y.val))

include continuous_f local_isometry in
/-- No global isometry of the cell inclusion is assumed: seam clearance supplies it locally,
then convex rigidity extends the developed motion across the entire cell. -/
theorem cell_isometry_of_boundary_gluing (i : I) (convex : Convex ℝ (cells i))
    (full : (interior (cells i)).Nonempty)
    (boundary : ∀ x ∈ seamSupport (fun i => cells i) glue i, x.val ∉ interior (cells i)) :
    Isometry (f ∘ of (fun i => cells i) glue i) := by
  apply isometry_of_interior_local_isometry convex full
    (f ∘ of (fun i => cells i) glue i)
    (continuous_f.comp (of_lipschitz (fun i => cells i) glue i).continuous)
  intro x
  let p : cells i := ⟨x.val, interior_subset x.property⟩
  obtain ⟨a, apos, ball_inside⟩ := Metric.isOpen_iff.mp isOpen_interior x.val x.property
  have clearance : ∀ z ∈ seamSupport (fun i => cells i) glue i, a ≤ dist z p := by
    intro z on_seam
    by_contra close
    exact boundary z on_seam (ball_inside (lt_of_not_ge close))
  obtain ⟨b, bpos, developed⟩ := local_isometry (of (fun i => cells i) glue i p)
  let r := min (a / 3) b
  have positive : 0 < r := lt_min (by positivity) bpos
  have clear : ∀ z ∈ seamSupport (fun i => cells i) glue i, 3 * r ≤ dist z p := by
    intro z hz
    have bound := clearance z hz
    have small : r ≤ a / 3 := min_le_left _ _
    linarith
  have cell_isometry := of_isometry_on_ball (fun i => cells i) glue i p positive.le clear
  let inclusion (y : Metric.ball x r) : Metric.ball p r :=
    ⟨⟨y.val.val, interior_subset y.val.property⟩, y.property⟩
  let lift (y : Metric.ball x r) : Metric.ball (of (fun i => cells i) glue i p) b :=
    ⟨of (fun i => cells i) glue i (inclusion y).val, by
      have nonexpanding : dist (of (fun i => cells i) glue i (inclusion y).val)
          (of (fun i => cells i) glue i p) ≤ dist (inclusion y).val p := by
        simpa only [NNReal.coe_one, one_mul] using
          (of_lipschitz (fun i => cells i) glue i).dist_le_mul (inclusion y).val p
      exact nonexpanding.trans_lt ((Metric.mem_ball.mp (inclusion y).property).trans_le
        (min_le_right _ _))⟩
  have lift_isometry : Isometry lift := by
    apply Isometry.of_dist_eq
    intro y z
    exact cell_isometry.dist_eq (inclusion y) (inclusion z)
  refine ⟨r, positive, ?_⟩
  apply Isometry.of_dist_eq
  intro y z
  exact developed.dist_eq (lift y) (lift z) |>.trans (lift_isometry.dist_eq y z)

/-- A planar isometry of the gluing gives rigid placements of the closed cells.
Distinct cells have disjoint developed interiors. -/
theorem exists_cell_placements_of_isometry
    (isometry : Isometry f) (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty)
    (boundary : ∀ i x, x ∈ seamSupport (fun i => cells i) glue i →
      x.val ∉ interior (cells i)) :
    ∃ A : I → Plane ≃ᵃⁱ[ℝ] Plane,
      (∀ i (x : cells i), A i x.val = f (of (fun i => cells i) glue i x)) ∧
      Pairwise (fun i j => Disjoint (A i '' interior (cells i)) (A j '' interior (cells j))) := by
  have local_iso (x : Realization (fun i => cells i) glue) :
      ∃ r > 0, Isometry (fun y : Metric.ball x r => f y.val) :=
    ⟨1, one_pos, fun y z => isometry y.val z.val⟩
  have placements (i : I) := exists_rigid_extension_convex (convex i) (full i)
    (f ∘ of (fun i => cells i) glue i)
    (cell_isometry_of_boundary_gluing cells glue f isometry.continuous local_iso i
      (convex i) (full i) (boundary i))
  choose A agrees using placements
  refine ⟨A, agrees, ?_⟩
  intro i j different
  rw [Set.disjoint_left]
  rintro w ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  let p : cells i := ⟨x, interior_subset hx⟩
  let q : cells j := ⟨y, interior_subset hy⟩
  have same := isometry.injective (((agrees i p).symm.trans hyx.symm).trans (agrees j q))
  obtain ⟨r, positive, inside⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have clear : ∀ z ∈ seamSupport (fun i => cells i) glue i, r ≤ dist z p := by
    intro z hz
    by_contra near
    exact boundary i z hz (inside (lt_of_not_ge near))
  have distance := clearance_le_edist_of_ne (fun i => cells i) glue (Ne.symm different)
    p q positive.le clear
  rw [same, edist_self] at distance
  exact (ENNReal.ofReal_pos.mpr positive).not_ge distance

end Unfoldings.MetricGluing
