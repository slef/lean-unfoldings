module

public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Geometry.RadialChain
public import Unfoldings.Topology.ChainInterval
public import Unfoldings.Geometry.ChainInterval

/-! Exact projected geometry of consecutive actual cut-bank windows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

variable {retain : Set C.Seam} {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- Taking a bank interval keeps every physical point with its original parameter. -/
theorem projectedBoundaryChain_interval_point (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) (t : unitInterval) :
    (F.projectedBoundaryChain (chain.interval first length fits)).point i t =
      (F.projectedBoundaryChain chain).point (chain.intervalIndex first length fits i) t :=
  (F.projectedBoundaryChain_point (chain.interval first length fits) i t).trans
    ((congrArg (fun p => Cap.horizontal (F.toSpace retain
      (C.directedBoundaryPath p t)))
        (chain.interval_point first length fits i)).trans
      (F.projectedBoundaryChain_point chain (chain.intervalIndex first length fits i) t).symm)

/-- Consecutive actual bank intervals are exactly the corresponding polygonal intervals,
including their true final endpoint. -/
theorem projectedBoundaryChain_interval (first length : ℕ) (fits : first + length ≤ n) :
    F.projectedBoundaryChain (chain.interval first length fits) =
      (F.projectedBoundaryChain chain).interval first (length + 1) (by omega) := by
  apply congrArg PolygonalChain.mk
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change (F.projectedBoundaryChain (chain.interval first length fits)).vertex
      (Fin.last (length + 1)) =
        (F.projectedBoundaryChain chain).vertex ⟨first + (length + 1), by omega⟩
    calc
      _ = (F.projectedBoundaryChain (chain.interval first length fits)).point
          (Fin.last length) 1 := by rw [PolygonalChain.point_one, Fin.succ_last]
      _ = (F.projectedBoundaryChain chain).point
          (chain.intervalIndex first length fits (Fin.last length)) 1 :=
        F.projectedBoundaryChain_interval_point chain first length fits _ _
      _ = _ := ((F.projectedBoundaryChain chain).point_one _).trans
        (congrArg (F.projectedBoundaryChain chain).vertex (Fin.ext (by
          change first + length + 1 = first + (length + 1)
          omega)))
  · change (F.projectedBoundaryChain (chain.interval first length fits)).vertex i.castSucc =
      (F.projectedBoundaryChain chain).vertex ⟨first + i.val, by omega⟩
    calc
      _ = (F.projectedBoundaryChain (chain.interval first length fits)).point i 0 :=
        ((F.projectedBoundaryChain (chain.interval first length fits)).point_zero i).symm
      _ = (F.projectedBoundaryChain chain).point (chain.intervalIndex first length fits i) 0 :=
        F.projectedBoundaryChain_interval_point chain first length fits _ _
      _ = _ := ((F.projectedBoundaryChain chain).point_zero _).trans
        (congrArg (F.projectedBoundaryChain chain).vertex (Fin.ext rfl))

/-- Radial order survives taking any consecutive actual bank window. -/
theorem projectedBoundaryChain_interval_radialFrom (first length : ℕ)
    (fits : first + length ≤ n) (source : Plane)
    (radial : (F.projectedBoundaryChain chain).RadialFrom source 0) :
    (F.projectedBoundaryChain (chain.interval first length fits)).RadialFrom source 0 := by
  intro i _ t s ordered
  dsimp only
  rw [F.projectedBoundaryChain_interval_point, F.projectedBoundaryChain_interval_point]
  exact radial (chain.intervalIndex first length fits i) (Nat.zero_le _) ordered

end Unfoldings.SpatialFolding
