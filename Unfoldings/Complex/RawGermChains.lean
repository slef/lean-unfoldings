module

public import Unfoldings.Complex.FaceRestrictionLinks
public import Unfoldings.Complex.LinkSteps
public import Unfoldings.Topology.ChainTerminalUniqueness

/-! Compare actual corner chains in one original raw-germ system, even after face restriction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Original corner turns and seam pairings without a chosen vertex-class subtype. -/
def rawGermSystem : PairedInvolutions.System C.Germ where
  turn := C.turnGerm
  mate := C.mateGerm Set.univ
  turn_involutive := C.turnGerm_involutive
  mate_involutive := C.mateGerm_involutive Set.univ
  turn_ne := C.turnGerm_ne

/-- All retained chain pairings are actual original pairings after restoring the cuts. -/
def rawLinkChain {retain : Set C.Seam} {w : C.Vertex retain} {n : ℕ}
    (c : (C.linkSystem retain w).Chain n) : C.rawGermSystem.Chain n where
  point i := (c.point i).val
  injective i j same := c.injective (Subtype.ext same)
  disjoint i j same := c.disjoint i j (Subtype.ext same)
  next i := by
    obtain ⟨s, _, side, b, first, last⟩ := C.chain_next_crosses retain w c i
    exact C.mateGerm_of_crossing ⟨s, Set.mem_univ _, side, b, first, last⟩

open Classical in
/-- Original face names and both original endpoint germs survive face restriction literally. -/
def rawRestrictedLinkChain (U : Set Face)
    {w : (C.restrictFaces U).Vertex Set.univ} {n : ℕ}
    (c : ((C.restrictFaces U).linkSystem Set.univ w).Chain n) : C.rawGermSystem.Chain n :=
  C.rawLinkChain (C.includeRestrictedLinkChain U c)

open Classical in
/-- Sum arbitrary original corner weights on an actual covering retained link chain. -/
theorem sum_ordered_link_corner_weights {retain : Set C.Seam} {w : C.Vertex retain} {n : ℕ}
    (c : (C.linkSystem retain w).Chain n) (covers : ∀ p, c.Visited p)
    (weight : C.Corner → ℝ) :
    (∑ i : Fin (n + 1), weight (c.point i).val.1) =
      ∑ a : C.Corner, if C.vertexOfCorner retain a = w then weight a else 0 := by
  classical
  have ordered := (C.linkCornerEquiv retain w c covers).sum_comp
    (fun a : C.CornerAt retain w => weight a.val)
  have subset := Finset.sum_subtype (F := (inferInstance : Fintype (C.CornerAt retain w)))
    (p := fun a : C.Corner => C.vertexOfCorner retain a = w) (Finset.univ.filter
    (fun a : C.Corner => C.vertexOfCorner retain a = w)) (by simp) weight
  exact ordered.trans ((Finset.sum_filter _ _).symm.trans subset).symm

end Unfoldings.TriangleComplex
