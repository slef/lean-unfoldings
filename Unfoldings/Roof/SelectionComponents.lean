module

public import Unfoldings.Roof.RestrictedDisk
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Whole-edge components of a convex-gradient roof selection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Face adjacency retains exactly the shared whole edges between selected faces.
Omitted faces are isolated vertices and are excluded by the selected-seed hypotheses. -/
def selectionGraph (slopes : Set Plane) : SimpleGraph Face where
  Adj f g := K.normalSlope f ∈ slopes ∧ K.normalSlope g ∈ slopes ∧
    TriangleFamily.EdgeAdjacent K.projectedTriangle f g
  symm := by
    constructor
    rintro f g ⟨hf, hg, different, e, h, same⟩
    exact ⟨hg, hf, different.symm, h, e, same.symm⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- Faces reached from a selected seed along selected whole-edge adjacencies. -/
def selectionComponent (slopes : Set Plane) (seed : Face) : Set Face :=
  ((K.selectionGraph slopes).connectedComponentMk seed).supp

@[simp] theorem seed_mem_selectionComponent (slopes : Set Plane) (seed : Face) :
    seed ∈ K.selectionComponent slopes seed :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_mem

theorem selectionComponent_selected {slopes : Set Plane} {seed : Face}
    (selected : K.normalSlope seed ∈ slopes) {f : Face}
    (member : f ∈ K.selectionComponent slopes seed) : K.normalSlope f ∈ slopes := by
  have reachable := ((K.selectionGraph slopes).connectedComponentMk seed).reachable_of_mem_supp
    (K.seed_mem_selectionComponent slopes seed) member
  have chain := ((K.selectionGraph slopes).reachable_iff_reflTransGen seed f).mp reachable
  induction chain with
  | refl => exact selected
  | tail _ step _ => exact step.2.1

open Classical in
/-- Every selected component has connected geometric interior. -/
theorem isConnected_interior_selectionComponent (slopes : Set Plane) (seed : Face) :
    IsConnected (interior (K.restrictedCarrier (K.selectionComponent slopes seed))) := by
  let component := (K.selectionGraph slopes).connectedComponentMk seed
  apply K.isConnected_interior_restrictedCarrier _ ⟨seed, K.seed_mem_selectionComponent slopes seed⟩
  intro f g
  have reachable := component.reachable_toSimpleGraph f.property g.property
  have chain := (component.toSimpleGraph.reachable_iff_reflTransGen f g).mp reachable
  refine Relation.ReflTransGen.mono ?_ f g chain
  intro a b adjacent
  exact ⟨fun same => adjacent.2.2.1 (congrArg Subtype.val same), adjacent.2.2.2⟩

end Unfoldings.ConvexRoof
