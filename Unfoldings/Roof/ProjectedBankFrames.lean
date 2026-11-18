module

public import Unfoldings.Roof.ProjectedBankMetric
public import Unfoldings.Development.BoundaryChainRolling
public import Unfoldings.Geometry.PlanePolarWindow
public import Unfoldings.Geometry.ComplexRotation
public import Unfoldings.Polyhedron.ProjectedBoundaryChain

/-! Exact common complex coordinates for physical projected banks and original intrinsic rolls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The identity projected development gives a common frame, allowing either orientation. -/
def projectedBankFrame {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) : Plane ≃ₗᵢ[ℝ] ℂ :=
  (K.projectedMetricDevelopment retain).boundaryCycleFrame (K.projectedMetricChain chain)

def projectedBankPhase {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) : ℝ :=
  (K.projectedBankFrame chain ((K.projectedMetricDevelopment retain).boundaryRay
    (K.projectedMetricChain chain).first)).arg

/-- The original intrinsic bank roll in the common frame's initial direction. -/
def framedIntrinsicRoll {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) : PolygonalChain ℂ (n + 1) :=
  (C.boundaryChainRoll chain).affineMap
    (complexRotation (K.projectedBankPhase chain)).toLinearMap.toAffineMap

theorem projectedMetric_boundaryRay {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    (K.projectedMetricDevelopment retain).boundaryRay
      (C.affineProjectionBoundaryEndEquiv K.projectFaceEquiv K.projectedTriangle_joined retain p) =
      Cap.horizontal (K.folding.germDirection p.val) := by
  let D := K.projectedMetricDevelopment retain
  let q := C.affineProjectionBoundaryEndEquiv K.projectFaceEquiv K.projectedTriangle_joined
    retain p
  have identity (f : Face) (x : Plane) : D.place f x = x := rfl
  have raw := D.boundaryRay_eq_raw q
  have far : D.germFarPoint q.val =
      (K.projectedMetricComplex.triangle q.val.1.1).vertex
        (K.projectedMetricComplex.germFarCorner q.val).2 := identity _ _
  rw [far, identity] at raw
  refine raw.trans ?_
  change K.projectFaceEquiv p.val.1.1 ((C.triangle p.val.1.1).vertex
      (C.germFarCorner p.val).2) - K.projectFaceEquiv p.val.1.1
      ((C.triangle p.val.1.1).vertex p.val.1.2) = Cap.horizontal (K.folding.germDirection p.val)
  exact (map_sub Cap.horizontal _ _).symm

/-- The actual projected edge is the canonical projected roll edge in one common frame. -/
theorem projectedBankFrame_edge {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    ((K.folding.projectedBoundaryChain chain).inComplexFrame
      (K.projectedBankFrame chain)).edge i =
      polarRay (K.projectedBankPhase chain) *
        (K.projectedMetricComplex.boundaryChainRoll (K.projectedMetricChain chain)).edge i := by
  let L := K.projectedBankFrame chain
  have coordinate : ((K.folding.projectedBoundaryChain chain).inComplexFrame L).edge i =
      L (Cap.horizontal (K.folding.germDirection (chain.point i).val)) := by
    change L ((K.folding.projectedBoundaryChain chain).vertex i.succ) -
      L ((K.folding.projectedBoundaryChain chain).vertex i.castSucc) = _
    rw [← map_sub, ← PolygonalChain.edge, K.folding.projectedBoundaryChain_edge]
  exact coordinate.trans ((congrArg L (K.projectedMetric_boundaryRay (chain.point i))).symm.trans
    ((K.projectedMetricDevelopment retain).boundaryChainRoll_edge_in_frame
      (K.projectedMetricChain chain) i))

/-- The common initial direction is a single rigid rotation of the intrinsic roll. -/
theorem framedIntrinsicRoll_edge {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.framedIntrinsicRoll chain).edge i =
      polarRay (K.projectedBankPhase chain) * (C.boundaryChainRoll chain).edge i := by
  change polarRay (K.projectedBankPhase chain) * (C.boundaryChainRoll chain).vertex i.succ -
    polarRay (K.projectedBankPhase chain) * (C.boundaryChainRoll chain).vertex i.castSucc = _
  rw [← mul_sub]
  rfl

/-- Framing preserves the full intrinsic rolled length. -/
theorem framedIntrinsicRoll_projectedLength {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) :
    (K.framedIntrinsicRoll chain).projectedLength =
      (C.boundaryChainRoll chain).projectedLength := by
  unfold PolygonalChain.projectedLength
  apply Finset.sum_congr rfl
  intro i _
  rw [K.framedIntrinsicRoll_edge, norm_mul, norm_polarRay, one_mul]

/-- Framing preserves the full intrinsic rolled chord. -/
theorem framedIntrinsicRoll_chord_norm {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) :
    ‖(K.framedIntrinsicRoll chain).vertex (Fin.last (n + 1)) -
      (K.framedIntrinsicRoll chain).vertex 0‖ =
      ‖(C.boundaryChainRoll chain).vertex (Fin.last (n + 1)) -
        (C.boundaryChainRoll chain).vertex 0‖ := by
  change ‖polarRay (K.projectedBankPhase chain) *
      (C.boundaryChainRoll chain).vertex (Fin.last (n + 1)) -
    polarRay (K.projectedBankPhase chain) * (C.boundaryChainRoll chain).vertex 0‖ = _
  rw [← mul_sub, norm_mul, norm_polarRay, one_mul]

/-- Physical projected coordinates realize the original exact phase and speed factors. -/
theorem framedIntrinsicRoll_edge_factor {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (K.framedIntrinsicRoll chain).edge i =
      (K.projectedMetricStretch (chain.point i) : ℂ) *
        polarRay (K.projectedMetricHeadingError chain i) *
          ((K.folding.projectedBoundaryChain chain).inComplexFrame
            (K.projectedBankFrame chain)).edge i := by
  rw [K.framedIntrinsicRoll_edge, K.projectedMetric_bank_edge_factor,
    K.projectedBankFrame_edge]
  ring

end Unfoldings.ConvexRoof
