module

public import Unfoldings.Cone.DirectedBankSector
public import Unfoldings.Complex.BoundaryLink
public import Unfoldings.Metric.BallIsometry

/-! Whole retained corner charts preserve the two literal directed boundary marks. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The apex of the intrinsic angular sector. -/
def closedAngularSectorOrigin {θ : ℝ} (nonnegative : 0 ≤ θ) :
    PolygonalPoint (closedAngularSector θ) :=
  ⟨0, ⟨0, 0, ⟨le_rfl, nonnegative⟩, by simp⟩⟩

namespace TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (p : C.BoundaryEnd retain) {Y : Type*} [EMetricSpace Y]
  (map : C.Realization retain → Y)

local notation "w" => C.boundaryEndVertex retain p
local notation "q" => C.boundaryMate retain p
local notation "θ" => C.totalAngle retain w
local notation "x" => map (C.vertexPoint retain w)

/-- In an actual whole-surface tangent chart the ordered link gives the intrinsic
sector and sends the two specified boundary paths to its two arclength rays. -/
theorem exists_directedIntervalChart (small : θ < 2 * Real.pi)
    (tangent_bank : ∀ (b : C.BoundaryEnd retain), C.boundaryEndVertex retain b = w →
      ∀ t : unitInterval, ENNReal.ofReal (t.val * C.boundaryBankLength b) =
        edist (map (C.directedBoundaryPath b t)) x)
    (tangent : ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball (C.tangentOrigin retain w) (ENNReal.ofReal r) ≃ᵢ
          Metric.eball x (ENNReal.ofReal r),
        ∀ (a : C.TangentTotal retain w)
          (near : edist (C.tangentPoint retain w a) (C.tangentOrigin retain w) < ENNReal.ofReal r),
          (chart ⟨C.tangentPoint retain w a, near⟩).val =
            map (C.tangentSurfaceTag retain w a)) :
    ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (closedAngularSectorOrigin (C.totalAngle_pos retain w).le)
            (ENNReal.ofReal r),
        (∀ (t : unitInterval)
          (near : edist (map (C.directedBoundaryPath p t)) x < ENNReal.ofReal r),
          (chart ⟨map (C.directedBoundaryPath p t), near⟩).val.val =
            (t.val * C.boundaryBankLength p : ℝ)) ∧
        (∀ (t : unitInterval)
          (near : edist (map (C.directedBoundaryPath q t)) x < ENNReal.ofReal r),
          (chart ⟨map (C.directedBoundaryPath q t), near⟩).val.val =
            (t.val * C.boundaryBankLength q) • polarRay θ) := by
  obtain ⟨n, c, first, last, covers⟩ := C.exists_boundary_link retain p
  have start : C.linkMate retain w c.first = c.first := by
    apply Subtype.ext
    change C.mateGerm retain c.first.val = c.first.val
    rw [first]
    exact (C.mateGerm_eq_self_iff retain p.val).mpr p.property
  have finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last := by
    apply Subtype.ext
    change C.mateGerm retain (C.linkTurn retain w c.last).val = _
    rw [last]
    let b := q
    exact (C.mateGerm_eq_self_iff retain b.val).mpr b.property
  obtain ⟨r, rpos, original, on_tags⟩ := tangent
  let sector := C.intervalSectorIsometryEquiv retain w c covers start finish small
  let o := closedAngularSectorOrigin (C.totalAngle_pos retain w).le
  have apex : sector (C.tangentOrigin retain w) = o :=
    PolygonalPoint.ext (C.intervalSectorIsometryEquiv_origin retain w c covers start finish small)
  let chart := original.symm.trans
    (basedEBallIsometry sector (C.tangentOrigin retain w) o apex (ENNReal.ofReal r))
  have trace (b : C.BoundaryEnd retain) (at_vertex : C.boundaryEndVertex retain b = w)
      (t : unitInterval) (near : edist (map (C.directedBoundaryPath b t)) x < ENNReal.ofReal r) :
      (chart ⟨map (C.directedBoundaryPath b t), near⟩).val =
        sector (C.tangentPoint retain w (C.directedBankTangentTag retain w b at_vertex t)) := by
    let y : Metric.eball x (ENNReal.ofReal r) := ⟨map (C.directedBoundaryPath b t), near⟩
    let tag := C.directedBankTangentTag retain w b at_vertex t
    have tag_near : edist (C.tangentPoint retain w tag) (C.tangentOrigin retain w) <
        ENNReal.ofReal r := by
      rw [C.edist_tangentPoint_directedBankTangentTag]
      exact (tangent_bank b at_vertex t).trans_lt near
    have image := on_tags tag tag_near
    rw [C.tangentSurfaceTag_directedBankTangentTag] at image
    have pre : original.symm y = ⟨C.tangentPoint retain w tag, tag_near⟩ :=
      original.injective (by
        rw [IsometryEquiv.apply_symm_apply]
        exact Subtype.ext image.symm)
    change sector (original.symm y).val = _
    rw [pre]
  exact ⟨r, rpos, chart,
    fun t near => (congrArg PolygonalPoint.val (trace p rfl t near)).trans
      (C.intervalSector_directedBankTangentTag_first retain w c covers start finish small p
        rfl first t),
    fun t near =>
      (congrArg PolygonalPoint.val (trace q (C.boundaryMate_spec retain p).2 t near)).trans
        (C.intervalSector_directedBankTangentTag_last retain w c covers start finish small q
          (C.boundaryMate_spec retain p).2 last t)⟩

end TriangleComplex
end Unfoldings
