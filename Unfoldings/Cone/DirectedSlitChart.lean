module

public import Unfoldings.Cone.DirectedBankSector
public import Unfoldings.Complex.BoundaryLink
public import Unfoldings.Complex.DirectedBoundaryPathReversal
public import Unfoldings.Metric.CenteredBallRestriction

/-! A directed corner chart preserves the two separate banks even at a full turn. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings

/-- A centered whole-ball chart in an angular fan with both actual bank marks.
The first bank is indexed by false, and the last by true. -/
structure MarkedSlitFanChart {X : Type*} [EMetricSpace X] (x : X)
    (θ : ℝ) (mark : Bool → unitInterval → X) (length : Bool → ℝ) (ρ : ℝ) where
  n : ℕ
  fan : AngularFan n
  angle_eq : fan.totalAngle = θ
  positive : 0 < ρ
  chart : Metric.eball x (ENNReal.ofReal ρ) ≃ᵢ Metric.eball fan.origin (ENNReal.ofReal ρ)
  center : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = fan.origin
  length_pos : ∀ b, 0 < length b
  radial : ∀ b t, edist (mark b t) x = ENNReal.ofReal (t.val * length b)
  at_bank : ∀ (b : Bool) (t : unitInterval)
    (near : edist (mark b t) x < ENNReal.ofReal ρ),
    let r : ℝ≥0 := ⟨t.val * length b, mul_nonneg t.property.1 (length_pos b).le⟩
    (chart ⟨mark b t, near⟩).val =
      if b then fan.faceMap (Fin.last n) (fan.finish (Fin.last n) r) else fan.faceMap 0 (fan.start 0 r)

namespace MarkedSlitFanChart

variable {X : Type*} [EMetricSpace X] {x : X}
  {θ : ℝ} {mark : Bool → unitInterval → X} {length : Bool → ℝ} {ρ : ℝ}

/-- Restrict the entire corner chart and both bank identities to a smaller radius. -/
def restrict (G : MarkedSlitFanChart x θ mark length ρ) {r : ℝ} (pos : 0 < r)
    (small : r ≤ ρ) : MarkedSlitFanChart x θ mark length r where
  n := G.n
  fan := G.fan
  angle_eq := G.angle_eq
  positive := pos
  chart := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr G.positive)
    (ENNReal.ofReal_le_ofReal small) G.chart G.center
  center := G.center
  length_pos := G.length_pos
  radial := G.radial
  at_bank := fun b t near => G.at_bank b t (near.trans_le (ENNReal.ofReal_le_ofReal small))

end MarkedSlitFanChart

namespace TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (p : C.BoundaryEnd retain) {Y : Type*} [EMetricSpace Y]
  (map : C.Realization retain → Y)

local notation "w" => C.boundaryEndVertex retain p
local notation "q" => C.boundaryMate retain p
local notation "x" => map (C.vertexPoint retain w)

/-- The whole tangent ball retains both directed marks as separate intrinsic rays. -/
theorem exists_directedSlitFanChart
    (tangent_bank : ∀ (b : C.BoundaryEnd retain), C.boundaryEndVertex retain b = w →
      ∀ t : unitInterval, ENNReal.ofReal (t.val * C.boundaryBankLength b) =
        edist (map (C.directedBoundaryPath b t)) x)
    (tangent : ∃ r : ℝ, 0 < r ∧
      ∃ chart : Metric.eball (C.tangentOrigin retain w) (ENNReal.ofReal r) ≃ᵢ
          Metric.eball x (ENNReal.ofReal r),
        ∀ (a : C.TangentTotal retain w)
          (near : edist (C.tangentPoint retain w a) (C.tangentOrigin retain w) < ENNReal.ofReal r),
          (chart ⟨C.tangentPoint retain w a, near⟩).val = map (C.tangentSurfaceTag retain w a)) :
    ∃ r, Nonempty (MarkedSlitFanChart x (C.totalAngle retain w)
      (fun b t => map (C.directedBoundaryPath (if b then q else p) t))
      (fun b => C.boundaryBankLength (if b then q else p)) r) := by
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
  let A := C.linkAngularFan retain w c
  let f := C.intervalFanIsometry retain w c covers start finish
  have apex : f A.origin = C.tangentOrigin retain w := C.angularToTangent_origin retain w c
  let equiv := (basedEBallIsometry f A.origin (C.tangentOrigin retain w) apex (ENNReal.ofReal r))
    |>.trans original
  let chart := equiv.symm
  let bank (b : Bool) := if b then q else p
  have at_w (b : Bool) : C.boundaryEndVertex retain (bank b) = w := by
    cases b
    · rfl
    · exact (C.boundaryMate_spec retain p).2
  have trace (b : Bool) (t : unitInterval)
      (near : edist (map (C.directedBoundaryPath (bank b) t)) x < ENNReal.ofReal r) :
      let s : ℝ≥0 := ⟨t.val * C.boundaryBankLength (bank b),
        mul_nonneg t.property.1 (C.boundaryBankLength_pos (bank b)).le⟩
      (chart ⟨map (C.directedBoundaryPath (bank b) t), near⟩).val = if b then
        A.faceMap (Fin.last n) (A.finish (Fin.last n) s) else A.faceMap 0 (A.start 0 s) := by
    let s : ℝ≥0 := ⟨t.val * C.boundaryBankLength (bank b),
      mul_nonneg t.property.1 (C.boundaryBankLength_pos (bank b)).le⟩
    let tag := C.directedBankTangentTag retain w (bank b) (at_w b) t
    let ray := if b then A.faceMap (Fin.last n) (A.finish (Fin.last n) s) else
      A.faceMap 0 (A.start 0 s)
    have ray_tag : f ray = C.tangentPoint retain w tag := by
      cases b
      · exact (C.directedBankTangentTag_first retain w c p (at_w false) first t).symm
      · exact (C.directedBankTangentTag_last retain w c q (at_w true) last t).symm
    have tag_near : edist (C.tangentPoint retain w tag) (C.tangentOrigin retain w) <
        ENNReal.ofReal r := by
      rw [C.edist_tangentPoint_directedBankTangentTag]
      exact (tangent_bank (bank b) (at_w b) t).trans_lt near
    have ray_near : edist ray A.origin < ENNReal.ofReal r := by
      rw [← f.isometry.edist_eq ray A.origin, apex, ray_tag]
      exact tag_near
    have tag_image := on_tags tag tag_near
    rw [C.tangentSurfaceTag_directedBankTangentTag] at tag_image
    have image : equiv ⟨ray, ray_near⟩ = ⟨map (C.directedBoundaryPath (bank b) t), near⟩ := by
      apply Subtype.ext
      change (original ⟨f ray, _⟩).val = _
      exact (congrArg (fun a => (original a).val) (Subtype.ext ray_tag)).trans tag_image
    exact congrArg Subtype.val (equiv.symm_apply_eq.mpr image.symm)
  have p_zero : map (C.directedBoundaryPath p 0) = x := congrArg map (C.directedBoundaryPath_zero p)
  have near_zero : edist (map (C.directedBoundaryPath p 0)) x < ENNReal.ofReal r := by
    rw [p_zero, edist_self]
    exact ENNReal.ofReal_pos.mpr rpos
  have centered : (chart ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val = A.origin := by
    have value := trace false 0 near_zero
    change (chart ⟨map (C.directedBoundaryPath p 0), near_zero⟩).val = _ at value
    rw [show (⟨map (C.directedBoundaryPath p 0), near_zero⟩ : Metric.eball x (ENNReal.ofReal r)) =
      ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ from Subtype.ext p_zero] at value
    exact value.trans (congrArg (fun s => A.faceMap 0 (A.start 0 s)) (NNReal.eq <| by
      change ((0 : unitInterval) : ℝ) * C.boundaryBankLength (bank false) = 0
      exact zero_mul _))
  exact ⟨r, ⟨⟨n, A, C.linkAngularFan_totalAngle retain w c covers, rpos, chart, centered,
    fun b => C.boundaryBankLength_pos _, fun b t => (tangent_bank _ (at_w b) t).symm, trace⟩⟩⟩

end TriangleComplex
end Unfoldings
