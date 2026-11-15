module

public import Unfoldings.Development.BoundaryRolling
public import Unfoldings.Complex.BoundaryChainAperture

/-! Realize actual finite boundary-chain rolling in one original development frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
  {n : ℕ} (chain : (C.boundarySystem retain).Chain n)

/-- A finite directed bank chain turns by the actual fan angle without any closing assumption. -/
theorem normalized_boundaryChain_step (k : Fin n) :
    NormedSpace.normalize (D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.succ))) =
      polarRay (Real.pi - C.totalAngle retain
        (C.boundaryEndVertex retain (chain.point k.succ))) *
          NormedSpace.normalize
            (D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.castSucc))) := by
  let θ := C.totalAngle retain (C.boundaryEndVertex retain (chain.point k.succ))
  have joined : C.boundaryMate retain (C.boundaryTurn retain (chain.point k.castSucc)) =
      chain.point k.succ := chain.next k
  have other := congrArg (C.boundaryMate retain) joined
  rw [C.boundaryMate_involutive] at other
  have rotation := D.normalized_boundaryMate_rotation chain k.succ
  rw [← other, D.boundaryRay_turn, map_neg, NormedSpace.normalize_neg] at rotation
  have inverse : polarRay (-θ) * polarRay θ = 1 := by
    rw [← polarRay_add, neg_add_cancel, polarRay_zero]
  have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
  have phase : polarRay (Real.pi - θ) = -polarRay (-θ) := by
    rw [sub_eq_add_neg, polarRay_add, half, neg_one_mul]
  calc
    _ = (polarRay (-θ) * polarRay θ) * NormedSpace.normalize
        (D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.succ))) := by
      rw [inverse, one_mul]
    _ = polarRay (-θ) * (-NormedSpace.normalize
        (D.boundaryCycleFrame chain (D.boundaryRay (chain.point k.castSucc)))) := by
      rw [mul_assoc, ← rotation]
    _ = _ := by rw [phase]; ring

/-- Each actual bank direction realizes its original unreduced finite-chain heading. -/
theorem normalized_boundaryChainRoll_heading (i : Fin (n + 1)) :
    NormedSpace.normalize (D.boundaryCycleFrame chain (D.boundaryRay (chain.point i))) =
      polarRay ((D.boundaryCycleFrame chain (D.boundaryRay chain.first)).arg +
        C.boundaryChainRollHeading chain i) := by
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rw [C.boundaryChainRollHeading_zero, add_zero]
    rw [show chain.point 0 = chain.first from rfl]
    exact complex_normalize_eq_polar_arg (by
      simpa only [map_zero] using (D.boundaryCycleFrame chain).injective.ne
        (D.boundaryRay_ne_zero chain.first))
  · rw [D.normalized_boundaryChain_step chain k, previous, ← polarRay_add]
    congr 1
    dsimp only [TriangleComplex.boundaryChainRollHeading]
    rw [Fin.partialSum_succ]
    ring

/-- The finite intrinsic roll has exactly the original developed edge vectors in one frame. -/
theorem boundaryChainRoll_edge_in_frame (i : Fin (n + 1)) :
    D.boundaryCycleFrame chain (D.boundaryRay (chain.point i)) =
      polarRay ((D.boundaryCycleFrame chain (D.boundaryRay chain.first)).arg) *
        (C.boundaryChainRoll chain).edge i := by
  let L := D.boundaryCycleFrame chain
  have magnitude : ‖L (D.boundaryRay (chain.point i))‖ =
      C.boundaryBankLength (chain.point i) := by rw [L.norm_map, D.boundaryRay_norm]
  calc
    _ = ‖L (D.boundaryRay (chain.point i))‖ •
        NormedSpace.normalize (L (D.boundaryRay (chain.point i))) :=
      (NormedSpace.norm_smul_normalize _).symm
    _ = _ := by
      rw [magnitude, D.normalized_boundaryChainRoll_heading,
        TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge,
        polarRay_add, Complex.real_smul]
      ring

/-- Original finite-chain adjacency gives the exact bank displacement in the development. -/
theorem boundaryRay_eq_chain_displacement (k : Fin n) :
    D.boundaryRay (chain.point k.castSucc) =
      D.boundaryPosition (chain.point k.succ) - D.boundaryPosition (chain.point k.castSucc) := by
  rw [D.boundaryRay_eq_positions]
  have paired := (C.boundaryMate_spec retain (C.boundaryTurn retain
    (chain.point k.castSucc))).2
  have joined : C.boundaryMate retain (C.boundaryTurn retain (chain.point k.castSucc)) =
      chain.point k.succ := chain.next k
  rw [joined] at paired
  exact congrArg (fun w => D.toPlane (C.vertexPoint retain w) -
    D.boundaryPosition (chain.point k.castSucc)) paired.symm

/-- The original finite roll places all named bank starts at their actual developed points. -/
theorem boundaryChainRoll_vertex_in_frame (i : Fin (n + 1)) :
    polarRay ((D.boundaryCycleFrame chain (D.boundaryRay chain.first)).arg) *
      (C.boundaryChainRoll chain).vertex i.castSucc =
        D.boundaryCycleFrame chain
          (D.boundaryPosition (chain.point i) - D.boundaryPosition chain.first) := by
  let P := C.boundaryChainRoll chain
  let L := D.boundaryCycleFrame chain
  let rotation := polarRay ((L (D.boundaryRay chain.first)).arg)
  change rotation * P.vertex i.castSucc =
    L (D.boundaryPosition (chain.point i) - D.boundaryPosition chain.first)
  refine Fin.induction ?_ (fun k previous => ?_) i
  · simp only [Fin.castSucc_zero, P, TriangleComplex.boundaryChainRoll,
      PolygonalChain.ofHeadings_start, mul_zero]
    rw [show chain.point 0 = chain.first from rfl, sub_self, map_zero]
  · have vector := D.boundaryChainRoll_edge_in_frame chain k.castSucc
    change L (D.boundaryRay (chain.point k.castSucc)) = rotation * P.edge k.castSucc at vector
    rw [D.boundaryRay_eq_chain_displacement chain k] at vector
    rw [PolygonalChain.edge, Fin.succ_castSucc] at vector
    rw [map_sub] at vector ⊢
    rw [map_sub] at previous
    rw [mul_sub] at vector
    linear_combination previous - vector

end Unfoldings.FacewiseDevelopment
