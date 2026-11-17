module

public import Unfoldings.Cap.ProjectedBoundaryChain
public import Unfoldings.Topology.ChainInterval
public import Unfoldings.Geometry.ChainInterval

/-! Exact projected geometry of consecutive actual cut-bank windows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance projectedIntervalMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n)

/-- Taking a bank interval keeps every physical point with its original parameter. -/
theorem projectedBoundaryChain_interval_point (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) (t : unitInterval) :
    (K.projectedBoundaryChain U (chain.interval first length fits)).point i t =
      (K.projectedBoundaryChain U chain).point (chain.intervalIndex first length fits i) t :=
  (K.projectedBoundaryChain_point U (chain.interval first length fits) i t).trans
    ((congrArg (fun p => Cap.horizontal ((K.folding.restrictFaces U).toSpace retain
      ((C.restrictFaces U).directedBoundaryPath p t)))
        (chain.interval_point first length fits i)).trans
      (K.projectedBoundaryChain_point U chain (chain.intervalIndex first length fits i) t).symm)

/-- Consecutive actual bank intervals are exactly the corresponding polygonal intervals,
including their true final endpoint. -/
theorem projectedBoundaryChain_interval (first length : ℕ) (fits : first + length ≤ n) :
    K.projectedBoundaryChain U (chain.interval first length fits) =
      (K.projectedBoundaryChain U chain).interval first (length + 1) (by omega) := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change (K.projectedBoundaryChain U (chain.interval first length fits)).vertex
      (Fin.last (length + 1)) =
        (K.projectedBoundaryChain U chain).vertex ⟨first + (length + 1), by omega⟩
    calc
      _ = (K.projectedBoundaryChain U (chain.interval first length fits)).point
          (Fin.last length) 1 := by rw [PolygonalChain.point_one, Fin.succ_last]
      _ = (K.projectedBoundaryChain U chain).point
          (chain.intervalIndex first length fits (Fin.last length)) 1 :=
        K.projectedBoundaryChain_interval_point U chain first length fits _ _
      _ = _ := ((K.projectedBoundaryChain U chain).point_one _).trans
        (congrArg (K.projectedBoundaryChain U chain).vertex (Fin.ext (by
          change first + length + 1 = first + (length + 1)
          omega)))
  · change (K.projectedBoundaryChain U (chain.interval first length fits)).vertex i.castSucc =
      (K.projectedBoundaryChain U chain).vertex ⟨first + i.val, by omega⟩
    calc
      _ = (K.projectedBoundaryChain U (chain.interval first length fits)).point i 0 :=
        ((K.projectedBoundaryChain U (chain.interval first length fits)).point_zero i).symm
      _ = (K.projectedBoundaryChain U chain).point (chain.intervalIndex first length fits i) 0 :=
        K.projectedBoundaryChain_interval_point U chain first length fits _ _
      _ = _ := ((K.projectedBoundaryChain U chain).point_zero _).trans
        (congrArg (K.projectedBoundaryChain U chain).vertex (Fin.ext rfl))

/-- Radial order survives taking any consecutive actual bank window. -/
theorem projectedBoundaryChain_interval_radialFrom (first length : ℕ)
    (fits : first + length ≤ n) (source : Plane)
    (radial : (K.projectedBoundaryChain U chain).RadialFrom source 0) :
    (K.projectedBoundaryChain U (chain.interval first length fits)).RadialFrom source 0 := by
  intro i _ t s ordered
  dsimp only
  rw [K.projectedBoundaryChain_interval_point, K.projectedBoundaryChain_interval_point]
  exact radial (chain.intervalIndex first length fits i) (Nat.zero_le _) ordered

end Unfoldings.ConvexCap
