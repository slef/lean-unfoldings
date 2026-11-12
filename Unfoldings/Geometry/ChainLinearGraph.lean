module

public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.WeakChainLinear
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-! A weakly coordinate-monotone chain with only flat zero steps is a genuine graph arc. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (height : E →L[ℝ] ℝ)
  (nonnegative : ∀ i, 0 ≤ height (P.edge i))
  (flat : ∀ i, height (P.edge i) = 0 → P.edge i = 0)

include nonnegative in
theorem path_linear_bounds {x : E} (member : x ∈ Set.range P.path) :
    height (P.vertex 0) ≤ height x ∧ height x ≤ height (P.vertex (Fin.last n)) := by
  have monotone := (P.monotone_linear_vertices_iff height.toLinearMap).mpr nonnegative
  rcases P.path_range.subset member with same | edge
  · rw [Set.mem_singleton_iff.mp same]
    exact ⟨le_rfl, monotone (Fin.zero_le _)⟩
  · obtain ⟨i, s, equal⟩ := Set.mem_iUnion.mp edge
    have formula : height (P.point i s) =
        (1 - (s : ℝ)) * height (P.vertex i.castSucc) + (s : ℝ) * height (P.vertex i.succ) :=
      P.linear_point height.toLinearMap i s
    rw [← equal, formula]
    have first := monotone (Fin.zero_le i.castSucc)
    have last := monotone (Fin.le_last i.succ)
    have ordered := monotone (Fin.castSucc_le_succ i)
    change height (P.vertex 0) ≤ height (P.vertex i.castSucc) at first
    change height (P.vertex i.succ) ≤ height (P.vertex (Fin.last n)) at last
    change height (P.vertex i.castSucc) ≤ height (P.vertex i.succ) at ordered
    change height (P.vertex 0) ≤ (1 - (s : ℝ)) * height (P.vertex i.castSucc) +
        (s : ℝ) * height (P.vertex i.succ) ∧
      (1 - (s : ℝ)) * height (P.vertex i.castSucc) + (s : ℝ) * height (P.vertex i.succ) ≤
        height (P.vertex (Fin.last n))
    constructor <;> nlinarith [s.property.1, s.property.2]

include nonnegative in
theorem path_linear_range : Set.range (fun s => height (P.path s)) =
    Set.Icc (height (P.vertex 0)) (height (P.vertex (Fin.last n))) := by
  apply Set.Subset.antisymm
  · rintro y ⟨s, rfl⟩
    exact P.path_linear_bounds height nonnegative (Set.mem_range_self s)
  · have connected := isPreconnected_range (height.continuous.comp P.path.continuous)
    apply connected.Icc_subset
    · exact ⟨0, congrArg height P.path.source⟩
    · exact ⟨1, congrArg height P.path.target⟩

include nonnegative flat in
theorem path_linear_injOn (positive : 0 < n) : Set.InjOn height (Set.range P.path) := by
  rintro x ⟨s, rfl⟩ y ⟨r, rfl⟩ equal
  obtain ⟨i, a, first⟩ := P.path_point_covered positive s
  obtain ⟨j, b, last⟩ := P.path_point_covered positive r
  rw [first, last] at equal ⊢
  exact P.point_eq_of_weak_linear_eq height.toLinearMap nonnegative flat i j a b equal

/-- The entire geometric path image is homeomorphic to its closed interval of
controlling coordinates. Flat edges and repeated vertices introduce no extra branches. -/
def linearGraphHomeomorph (positive : 0 < n) :
    Set.range P.path ≃ₜ Set.Icc (height (P.vertex 0)) (height (P.vertex (Fin.last n))) := by
  let coordinate : Set.range P.path →
      Set.Icc (height (P.vertex 0)) (height (P.vertex (Fin.last n))) :=
    fun x => ⟨height x.val, P.path_linear_bounds height nonnegative x.property⟩
  have injective : Function.Injective coordinate := by
    intro x y equal
    exact Subtype.ext (P.path_linear_injOn height nonnegative flat positive x.property y.property
      (congrArg Subtype.val equal))
  have surjective : Function.Surjective coordinate := by
    intro y
    obtain ⟨s, equal⟩ := (P.path_linear_range height nonnegative).symm.subset y.property
    exact ⟨⟨P.path s, Set.mem_range_self s⟩, Subtype.ext equal⟩
  letI : CompactSpace (Set.range P.path) :=
    isCompact_iff_compactSpace.mp (isCompact_range P.path.continuous)
  let equivalence := Equiv.ofBijective coordinate ⟨injective, surjective⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := equivalence)
    ((height.continuous.comp continuous_subtype_val).subtype_mk _)

@[simp] theorem linearGraphHomeomorph_apply (positive : 0 < n) (x : Set.range P.path) :
    (P.linearGraphHomeomorph height nonnegative flat positive x).val = height x.val := rfl

end Unfoldings.PolygonalChain
