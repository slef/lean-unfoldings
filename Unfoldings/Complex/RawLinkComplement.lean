module

public import Unfoldings.Complex.RawGermChains
public import Unfoldings.Complex.ComplementaryLinkChains

/-! Opposite original raw fan chains partition the entire intrinsic vertex link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {n m : ℕ} (c : C.rawGermSystem.Chain n)

/-- An original raw link chain stays at one actual original vertex. -/
theorem rawGermChain_vertex (i : Fin (n + 1)) :
    C.vertexOfCorner Set.univ (c.point i).1 = C.vertexOfCorner Set.univ c.first.1 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k previous =>
    rw [← c.next k]
    change C.vertexOfCorner Set.univ (C.mateGerm Set.univ (C.turnGerm (c.point k.castSucc))).1 = _
    rw [C.mateGerm_vertex_eq]
    exact previous

/-- Restore a raw fan's intrinsic original vertex class without changing any interval labels. -/
def rawChainAtVertex (w : C.Vertex Set.univ)
    (first : C.vertexOfCorner Set.univ c.first.1 = w) : (C.linkSystem Set.univ w).Chain n where
  point i := ⟨c.point i, (C.rawGermChain_vertex c i).trans first⟩
  injective := fun _ _ same => c.injective (congrArg Subtype.val same)
  disjoint i j same := c.disjoint i j (congrArg Subtype.val same)
  next i := Subtype.ext (c.next i)

/-- Original opposite terminal seam pairings determine exact complementary corner sums.
The two fan lengths and all intermediate original corner labels may differ. -/
theorem sum_opposite_raw_linkCornerWeight (d : C.rawGermSystem.Chain m)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ c.first.1))
    (first : d.first = C.mateGerm Set.univ c.first)
    (last : C.turnGerm d.last = C.mateGerm Set.univ (C.turnGerm c.last))
    (different : C.turnGerm d.last ≠ c.first) (weight : C.Corner → ℝ) :
    (∑ i, weight (c.point i).1) + (∑ j, weight (d.point j).1) =
      C.regionalCornerSum Set.univ weight (C.vertexOfCorner Set.univ c.first.1) := by
  let w := C.vertexOfCorner Set.univ c.first.1
  let left := C.rawChainAtVertex c w rfl
  have original : C.vertexOfCorner Set.univ d.first.1 = w := by
    rw [first, C.mateGerm_vertex_eq]
  let right := C.rawChainAtVertex d w original
  have paired_first : right.first = (C.linkSystem Set.univ w).mate left.first :=
    Subtype.ext first
  have paired_last : (C.linkSystem Set.univ w).turn right.last =
      (C.linkSystem Set.univ w).mate ((C.linkSystem Set.univ w).turn left.last) :=
    Subtype.ext last
  have distinct : (C.linkSystem Set.univ w).turn right.last ≠ left.first := by
    intro same
    exact different (congrArg Subtype.val same)
  exact C.sum_opposite_linkCornerWeight left right internal paired_first paired_last distinct weight

end Unfoldings.TriangleComplex
