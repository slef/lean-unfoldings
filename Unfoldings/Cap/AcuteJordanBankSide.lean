module

public import Unfoldings.Cap.AcuteOriginalBankBudget
public import Unfoldings.Cap.JordanRegionalAngles
public import Unfoldings.Geometry.AcuteChainBankSide

/-! Select the two-link closure on the side of the original physical bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

local instance acuteBankSideMembership (U : Set Face) : DecidablePred (· ∈ U) :=
  Classical.decPred _

private theorem projected_mate_edge_eq (p : C.Germ) :
    let q := C.mateGerm Set.univ p
    (K.projectedTriangle q.1.1).edge (C.germEdge q).edge =
      (K.projectedTriangle p.1.1).edge (C.germEdge p).edge := by
  dsimp only
  by_cases boundary : C.IsBoundaryEdge Set.univ (C.germEdge p)
  · rw [(C.mateGerm_eq_self_iff Set.univ p).mpr boundary]
  · obtain ⟨q, crosses⟩ := (C.exists_germCrosses_iff Set.univ p).mpr boundary
    rw [C.mateGerm_of_crossing crosses]
    obtain ⟨seam, _, side, flag, rfl, rfl⟩ := crosses
    simp only [C.germEdge_germOfEndpoint]
    cases side
    · exact (K.projected_seam_edges_eq seam).symm
    · exact K.projected_seam_edges_eq seam

variable (U : Set Face) {retain : Set (C.restrictFaces U).Seam} {n : ℕ}
  (chain : ((C.restrictFaces U).boundarySystem retain).Chain n)

private theorem projected_chain_point_mem_bankEdge (i : Fin (n + 1)) (t : unitInterval) :
    (K.projectedBoundaryChain U chain).point i t ∈
      (K.projectedTriangle (chain.point i).val.1.1.val).edge
        (C.germEdge (C.includeRestrictedGerm U (chain.point i).val)).edge := by
  rw [K.projectedBoundaryChain_point, ConvexCap.projectedTriangle, Triangle.affineImage_edge]
  let R := C.restrictFaces U
  let bank := (R.boundaryEndEquiv retain (chain.point i)).1
  let parameter := R.bankParameterFromEnd bank (R.boundaryEndEquiv retain (chain.point i)).2 t
  exact ⟨parameter.val, parameter.property, rfl⟩

local notation "P" => K.projectedBoundaryChain U chain

/-- The two regular closures lie on opposite sides of the initial bank.
At least one leaves the actual opposite incident triangle outside its disk. -/
theorem not_mem_mate_face_of_one_acute_closure (h k : Plane →L[ℝ] ℝ)
    (first : ∀ i : Fin (n + 1), 0 < h ((P).edge i))
    (last : ∀ i : Fin (n + 1), 0 < k ((P).edge i))
    (joint : Function.Injective fun p => (h p, k p))
    (low high : Plane)
    (low_initial : h low ≤ h ((P).vertex 0))
    (low_terminal : k ((P).vertex (Fin.last (n + 1))) ≤ k low)
    (high_initial : k high ≤ k ((P).vertex 0))
    (high_terminal : h ((P).vertex (Fin.last (n + 1))) ≤ h high)
    (jordan_low : Schoenflies.IsJordanCurve ((P).twoLinkClosure low))
    (jordan_high : Schoenflies.IsJordanCurve ((P).twoLinkClosure high))
    (avoid_low : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) ((P).twoLinkClosure low))
    (avoid_high : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) ((P).twoLinkClosure high)) :
    let face := (C.mateGerm Set.univ (C.includeRestrictedGerm U chain.first.val)).1.1
    face ∉ K.jordanFaces ((P).twoLinkClosure low) ∨
      face ∉ K.jordanFaces ((P).twoLinkClosure high) := by
  let path := P
  let g := C.includeRestrictedGerm U chain.first.val
  let mate := C.mateGerm Set.univ g
  let T := K.projectedTriangle mate.1.1
  let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let a := path.vertex 0
  let b := path.vertex (0 : Fin (n + 1)).succ
  let p := path.point 0 t
  let L := h + k
  have on_mate (s : unitInterval) : path.point 0 s ∈ T.edge (C.germEdge mate).edge :=
    (K.projected_mate_edge_eq g).symm.subset (K.projected_chain_point_mem_bankEdge U chain 0 s)
  have left_edge : a ∈ T.edge (C.germEdge mate).edge := by
    have at_zero := on_mate 0
    change AffineMap.lineMap a b (0 : ℝ) ∈ T.edge (C.germEdge mate).edge at at_zero
    simpa only [AffineMap.lineMap_apply_zero] using at_zero
  have right_edge : b ∈ T.edge (C.germEdge mate).edge := by
    have at_one := on_mate 1
    change AffineMap.lineMap a b (1 : ℝ) ∈ T.edge (C.germEdge mate).edge at at_one
    simpa only [AffineMap.lineMap_apply_one] using at_one
  have inside_excluded : p ∉ interior T.carrier := by
    intro inside
    have zero := T.coord_edge_eq_zero (C.germEdge mate).edge ⟨p, on_mate t⟩
    exact ((T.interior_eq_pos_coord.subset inside _).ne') zero
  have progress (i : Fin (n + 1)) : 0 < L (path.edge i) := add_pos (first i) (last i)
  have increase : L a < L b := by
    exact (path.strictMono_linear_vertices L progress) (Fin.castSucc_lt_succ (i := (0 : Fin (n + 1))))
  have value : L p = (L a + L b) / 2 := by
    change L.toLinearMap.toAffineMap (AffineMap.lineMap a b (1 / 2 : ℝ)) = _
    rw [L.toLinearMap.toAffineMap.apply_lineMap]
    change AffineMap.lineMap (L a) (L b) (1 / 2 : ℝ) = _
    rw [AffineMap.lineMap_apply_ring]
    ring
  have beyond := (path.strictMono_linear_vertices L progress).monotone (Fin.le_last (0 : Fin (n + 1)).succ)
  change L b ≤ L (path.vertex (Fin.last (n + 1))) at beyond
  have not_first : p ≠ a := fun eq => by rw [eq] at value; linarith only [increase, value]
  have not_last : p ≠ path.vertex (Fin.last (n + 1)) := fun eq => by
    rw [eq] at value
    linarith only [value, increase, beyond]
  have excluded := path.adjacent_body_not_subset_one_twoLink_domain h k first last
    (Nat.succ_pos n) joint low high low_initial low_terminal high_initial high_terminal
    (path.point_mem_path_range 0 t) not_first not_last T.carrier
    T.convex_carrier T.interior_nonempty inside_excluded (T.edge_subset _ left_edge)
    (T.edge_subset _ right_edge)
    (show L a < L p by linarith only [value, increase])
    (show L p < L b by linarith only [value, increase])
  exact excluded.imp
    (fun hole present => hole (K.jordanFace_subset_domain jordan_low avoid_low mate.1.1 present))
    (fun hole present => hole (K.jordanFace_subset_domain jordan_high avoid_high mate.1.1 present))

end Unfoldings.ConvexCap
