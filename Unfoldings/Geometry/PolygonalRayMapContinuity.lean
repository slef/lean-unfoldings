module

public import Unfoldings.Geometry.PolygonalRayTransfer
public import Unfoldings.Geometry.LineCoordinate
public import Unfoldings.Geometry.ChainSplit
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! The exact map of original addresses is continuous, including the finite-to-tail join. -/

@[expose] public section

noncomputable section

open scoped NNReal RealInnerProductSpace

namespace Unfoldings.PolygonalRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} (B : PolygonalRay E n)
  (outward : B.Outward) (genuine : ∀ i, B.chain.edge i ≠ 0)
  (nonzero : B.direction ≠ 0) (Q : PolygonalRay F n)

private theorem continuous_lineCoordinate (p q : E) : Continuous (lineCoordinate p q) := by
  change Continuous (fun x : E => ⟪q - p, q - p⟫⁻¹ * ⟪q - p, x - p⟫)
  exact continuous_const.mul (continuous_const.inner (continuous_id.sub continuous_const))

private theorem lineCoordinate_advance (p d : E) (genuine : d ≠ 0) (t : ℝ) :
    lineCoordinate p (p + d) (p + t • d) = t := by
  have different : p ≠ p + d := fun eq => genuine (by
    have h := congrArg (· - p) eq
    simpa using h.symm)
  have line : AffineMap.lineMap p (p + d) t = p + t • d := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  rw [← line, lineCoordinate_lineMap different]

include outward genuine nonzero in
/-- Transfer to the target chain is continuous on the whole original closed bank.
Each edge and the entire tail use an affine formula for their original parameter. -/
theorem continuous_mapCarrier : Continuous (B.mapCarrier Q) := by
  apply Continuous.subtype_mk
  let patch : Fin n ⊕ Unit → Set B.carrier :=
    Sum.elim (fun i => Subtype.val ⁻¹' Set.range (B.chain.point i))
      (fun _ => Subtype.val ⁻¹' Set.range B.tail)
  have closed (i : Fin n ⊕ Unit) : IsClosed (patch i) := by
    cases i with
    | inl i =>
      apply IsClosed.preimage continuous_subtype_val
      exact (isCompact_range (Path.segment (B.chain.vertex i.castSucc)
        (B.chain.vertex i.succ)).continuous).isClosed
    | inr i => exact (B.isClosed_range_tail nonzero).preimage continuous_subtype_val
  have cover : (⋃ i, patch i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, eq⟩ := B.exists_address x.property
    cases a with
    | inl it => exact Set.mem_iUnion.mpr ⟨.inl it.1, it.2, eq⟩
    | inr t => exact Set.mem_iUnion.mpr ⟨.inr (), t, eq⟩
  apply (locallyFinite_of_finite patch).continuous cover closed
  intro i
  cases i with
  | inl i =>
    let p := B.chain.vertex i.castSucc
    let q := B.chain.vertex i.succ
    let g (x : B.carrier) := Q.chain.vertex i.castSucc +
      lineCoordinate p q x.val • Q.chain.edge i
    have cont : Continuous g :=
      continuous_const.add (((continuous_lineCoordinate p q).comp continuous_subtype_val).smul
        continuous_const)
    refine cont.continuousOn.congr ?_
    intro x hx
    obtain ⟨t, equal⟩ : x.val ∈ Set.range (B.chain.point i) := hx
    have tag : (⟨B.addressPoint (.inl (i, t)), B.addressPoint_mem (.inl (i, t))⟩ : B.carrier) = x :=
      Subtype.ext equal
    have transfer := congrArg Subtype.val (B.mapCarrier_address outward genuine nonzero Q
      (.inl (i, t)))
    rw [tag] at transfer
    change (B.mapCarrier Q x).val = Q.chain.point i t at transfer
    change (B.mapCarrier Q x).val = g x
    rw [transfer]
    have different : p ≠ q := fun equal => genuine i (sub_eq_zero.mpr equal.symm)
    have parameter : lineCoordinate p q x.val = t.val :=
      (congrArg (lineCoordinate p q) equal).symm.trans (lineCoordinate_lineMap different t.val)
    change AffineMap.lineMap _ _ _ = Q.chain.vertex i.castSucc + _ • Q.chain.edge i
    rw [parameter, AffineMap.lineMap_apply_module', add_comm]
    rfl
  | inr i =>
    let p := B.chain.vertex (Fin.last n)
    let g (x : B.carrier) := Q.chain.vertex (Fin.last n) +
      lineCoordinate p (p + B.direction) x.val • Q.direction
    have cont : Continuous g := continuous_const.add
      (((continuous_lineCoordinate p (p + B.direction)).comp continuous_subtype_val).smul
        continuous_const)
    refine cont.continuousOn.congr ?_
    intro x hx
    obtain ⟨t, equal⟩ : x.val ∈ Set.range B.tail := hx
    have tag : (⟨B.addressPoint (.inr t), B.addressPoint_mem (.inr t)⟩ : B.carrier) = x :=
      Subtype.ext equal
    have transfer := congrArg Subtype.val (B.mapCarrier_address outward genuine nonzero Q (.inr t))
    rw [tag] at transfer
    change (B.mapCarrier Q x).val = Q.tail t at transfer
    change (B.mapCarrier Q x).val = g x
    rw [transfer]
    have parameter : lineCoordinate p (p + B.direction) x.val = (t : ℝ) :=
      (congrArg (lineCoordinate p (p + B.direction)) equal).symm.trans
        (lineCoordinate_advance p B.direction nonzero t)
    change Q.tail t = Q.chain.vertex (Fin.last n) +
      lineCoordinate p (p + B.direction) x.val • Q.direction
    rw [parameter]
    rfl

include outward genuine nonzero in
/-- The arclength transport is proper when the target has a genuine infinite tail. -/
theorem isProperMap_mapCarrier (target_nonzero : Q.direction ≠ 0) :
    IsProperMap (B.mapCarrier Q) := by
  have continuous := B.continuous_mapCarrier outward genuine nonzero Q
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous, ?_⟩
  intro s compact
  let tip := Q.chain.vertex (Fin.last n)
  obtain ⟨r, bound⟩ := (compact.image continuous_subtype_val).isBounded.subset_closedBall tip
  let limit := (r / ‖Q.direction‖).toNNReal
  let K := Set.range B.chain.path ∪ B.tail '' Set.Icc 0 limit
  have bounded : IsCompact K := (isCompact_range B.chain.path.continuous).union
    (isCompact_Icc.image B.continuous_tail)
  have small : IsCompact ((↑) ⁻¹' K : Set B.carrier) :=
    (B.isClosed_carrier nonzero).isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage bounded
  apply small.of_isClosed_subset (compact.isClosed.preimage continuous)
  intro x hx
  obtain ⟨address, equal⟩ := B.exists_address x.property
  cases address with
  | inl it =>
    exact Or.inl (equal ▸ B.chain.point_mem_path_range it.1 it.2)
  | inr t =>
    let z : B.carrier := ⟨B.tail t, B.tail_mem t⟩
    have x_eq : z = x := Subtype.ext equal
    have target : Q.tail t ∈ Metric.closedBall tip r := by
      apply bound
      refine ⟨B.mapCarrier Q x, hx, ?_⟩
      exact (congrArg Subtype.val ((congrArg (B.mapCarrier Q) x_eq).symm.trans
        (B.mapCarrier_address outward genuine nonzero Q (.inr t))))
    have speed : dist (Q.tail t) tip = (t : ℝ) * ‖Q.direction‖ := by
      change dist (tip + (t : ℝ) • Q.direction) tip = _
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact congrArg (· * ‖Q.direction‖)
        (Real.norm_of_nonneg (show 0 ≤ (t : ℝ) from t.property))
    have le : (t : ℝ) ≤ r / ‖Q.direction‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr target_nonzero)).mpr
        (speed.symm.trans_le (Metric.mem_closedBall.mp target))
    have fit : t ≤ limit := le.trans (Real.le_coe_toNNReal _)
    exact Or.inr ⟨t, ⟨zero_le, fit⟩, equal⟩

end Unfoldings.PolygonalRay
