module

public import Unfoldings.Cap.ClipOriginalCopies
public import Mathlib.Topology.LocallyFinite

/-! Continuous maps from each whole original projected face into its retained fine subdivision. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalFaceMapIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
def originalFaceMap (lower : Z < 0) (retain : Set C.Seam) (f : Face)
    (p : (K.projectedTriangle f).carrier) :
    L.originalComplex.Realization (L.originalRetain retain) :=
  let covered := L.original_piece_cover lower f p.val p.property
  L.originalPointCopy retain covered.choose p.val covered.choose_spec.2

open Classical in
theorem originalFaceMap_eq (lower : Z < 0) (retain : Set C.Seam) (f : Face)
    (p : (K.projectedTriangle f).carrier) (i : L.originalPieceSet)
    (parent : L.originalParent i = f)
    (member : p.val ∈ (L.partition.projectedTriangle i.val).carrier) :
    L.originalFaceMap lower retain f p = L.originalPointCopy retain i p.val member := by
  let covered := L.original_piece_cover lower f p.val p.property
  exact L.originalPointCopy_eq_of_same_parent lower retain
    (covered.choose_spec.1.trans parent.symm) p.val covered.choose_spec.2 member

open Classical in
theorem originalFaceMap_continuous (lower : Z < 0) (retain : Set C.Seam) (f : Face) :
    Continuous (L.originalFaceMap lower retain f) := by
  let I := {i : L.originalPieceSet // L.originalParent i = f}
  let piece (i : I) : Set (K.projectedTriangle f).carrier :=
    {p | p.val ∈ (L.partition.projectedTriangle i.val.val).carrier}
  have closed (i : I) : IsClosed (piece i) :=
    (L.partition.projectedTriangle i.val.val).compact_carrier.isClosed.preimage
      continuous_subtype_val
  have cover : (⋃ i, piece i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨i, parent, member⟩ := L.original_piece_cover lower f p.val p.property
    exact Set.mem_iUnion.mpr ⟨⟨i, parent⟩, member⟩
  have branch (i : I) : ContinuousOn (L.originalFaceMap lower retain f) (piece i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have equal : (fun p : piece i => L.originalFaceMap lower retain f p.val) =
        fun p : piece i => L.originalComplex.faceMap (L.originalRetain retain) i.val
          ⟨(K.projectFaceEquiv (L.partition.face i.val.val)).symm p.val.val,
            (L.partition.triangle_carrier i.val.val).symm.subset
              ⟨p.val.val, p.property, rfl⟩⟩ := by
      funext p
      exact L.originalFaceMap_eq lower retain f p.val i.val i.property p.property
    change Continuous (fun p : piece i => L.originalFaceMap lower retain f p.val)
    rw [equal]
    apply (L.originalComplex.faceMap_lipschitz (L.originalRetain retain) i.val).continuous.comp
    apply Continuous.subtype_mk
    let chart := (K.projectFaceEquiv (L.partition.face i.val.val)).symm.toAffineMap
    have continuous := chart.continuous_of_finiteDimensional
    exact continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have all := (locallyFinite_of_finite piece).continuousOn_iUnion closed branch
  rw [cover] at all
  exact continuousOn_univ.mp all

end Unfoldings.ConvexCap.LineAlignedClip
