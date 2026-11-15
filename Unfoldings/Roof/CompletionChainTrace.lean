module

public import Unfoldings.Roof.CompletionChainFanRefinement
public import Unfoldings.Complex.BoundaryChainTrace

/-! Whole intrinsic bank traces agree exactly under the physical completion isometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainTraceIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Original bank labels agree with the actual old chain, independently of endpoint direction. -/
theorem label_bank (i : Fin (n + 1)) :
    (C.boundaryEndEquiv retain (coarse.point i)).1 = (R.label i).bank := by
  rw [← R.named]
  exact congrArg Prod.fst ((C.boundaryEndEquiv retain).apply_symm_apply _)

open Classical in
/-- The whole fine trace has exactly the old metric image, retaining all cut-side copies. -/
theorem trace_image :
    E.originalMetricEquiv retain '' E.originalComplex.boundaryChainTrace R.chain =
      C.boundaryChainTrace coarse := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  ext x
  constructor
  · rintro ⟨y, member, rfl⟩
    obtain ⟨j, on_bank⟩ := Set.mem_iUnion.mp member
    obtain ⟨i, k, same⟩ := (R.covered (R.chain.point j)).mp ⟨j, rfl⟩
    change (R.block i).chain.point k = R.chain.point j at same
    have named := (R.block i).named k
    rw [same] at named
    change y ∈ Set.range (D.bankMap kept (D.boundaryEndEquiv kept (R.chain.point j)).1)
      at on_bank
    rw [named] at on_bank
    obtain ⟨z, rfl⟩ := on_bank
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [R.label_bank]
    change _ ∈ Set.range (C.bankMap retain
      (C.cutBank retain (R.label i).seam (R.label i).side))
    rw [E.original_cutBank_eq_union_subdivided]
    exact Set.mem_iUnion.mpr ⟨(R.block i).index k, z, rfl⟩
  · intro member
    obtain ⟨i, on_bank⟩ := Set.mem_iUnion.mp member
    change x ∈ Set.range (C.bankMap retain
      (C.boundaryEndEquiv retain (coarse.point i)).1) at on_bank
    rw [R.label_bank] at on_bank
    change x ∈ Set.range (C.bankMap retain
      (C.cutBank retain (R.label i).seam (R.label i).side)) at on_bank
    rw [E.original_cutBank_eq_union_subdivided] at on_bank
    obtain ⟨a, z, at_x⟩ := Set.mem_iUnion.mp on_bank
    obtain ⟨k, at_a⟩ := (R.block i).index.surjective a
    obtain ⟨j, same⟩ := (R.covered ((R.block i).chain.point k)).mpr ⟨i, k, rfl⟩
    have named := (R.block i).named k
    rw [← same, at_a] at named
    refine ⟨D.bankMap kept (E.subdividedCutBank retain (R.label i).seam (R.label i).side a) z,
      ?_, at_x⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change _ ∈ Set.range (D.bankMap kept (D.boundaryEndEquiv kept (R.chain.point j)).1)
    rw [named]
    exact ⟨z, rfl⟩

open Classical in
/-- Every physical observation of a whole fine bank trace has exactly the old trace image. -/
theorem observed_trace_image {Y : Type*} (observe : C.Realization retain → Y) :
    (observe ∘ E.originalMetricEquiv retain) ''
        E.originalComplex.boundaryChainTrace R.chain =
      observe '' C.boundaryChainTrace coarse := by
  rw [Set.image_comp, R.trace_image]

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
