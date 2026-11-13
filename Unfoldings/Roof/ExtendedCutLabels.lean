module

public import Unfoldings.Roof.OriginalCutLabels
public import Unfoldings.Roof.SkirtRimComponents
public import Unfoldings.Roof.ExtendedGeometricCuts
public import Unfoldings.Roof.ParentRadialGrowth
public import Unfoldings.Geometry.LocalRadialGrowth

/-! Consistent radial-component labels for every actual original cut and skirt continuation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))

abbrev ExtendedCutPiece := {w : C.Vertex Set.univ // w ∉ M.parents.roots} ⊕ F.Component

def cutPieceFirst : M.ExtendedCutPiece F → Plane :=
  Sum.elim (fun e => K.projectedVertex e.val) F.componentSeed

def cutPieceLast : M.ExtendedCutPiece F → Plane :=
  Sum.elim (fun e => K.projectedVertex (M.parents.parent e.val))
    (fun c => (F.componentTail c).tip)

local instance extendedPieceSeedFinite : Finite F.Index := F.finite
local instance extendedPieceComponentFinite : Finite F.Component :=
  RadialTailFamily.finiteComponent F.tail

theorem extendedGeometricCuts_eq_piece_union :
    M.extendedGeometricCuts F =
      ⋃ i : M.ExtendedCutPiece F, segment ℝ (M.cutPieceFirst F i) (M.cutPieceLast F i) := by
  ext p
  constructor
  · rintro (original | skirt)
    · obtain ⟨e, member⟩ := Set.mem_iUnion.mp original
      exact Set.mem_iUnion.mpr ⟨Sum.inl e, member⟩
    · obtain ⟨c, member⟩ := Set.mem_iUnion.mp skirt
      exact Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩
  · rintro member
    obtain ⟨e | c, member⟩ := Set.mem_iUnion.mp member
    · exact Or.inl (Set.mem_iUnion.mpr ⟨e, member⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨c, member⟩)

theorem cutPiece_outward (positive : 0 < t) (small : t < 1) (i : M.ExtendedCutPiece F) :
    0 ≤ inner ℝ (M.cutPieceFirst F i - origin)
      (M.cutPieceLast F i - M.cutPieceFirst F i) := by
  cases i with
  | inl e => exact M.parent_radial_outward positive small e
  | inr c => exact (F.componentTail c).radial_outward

variable (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
  K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)

def cutPieceLabel : M.ExtendedCutPiece F → F.Component :=
  Sum.elim (fun e => F.rimComponent covered (M.parents.root e.val) (M.rootPath_end_boundary e.val))
    (fun c => c)

theorem parentPiece_label_of_tail_intersection
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) (c : F.Component) {p : Plane}
    (old : p ∈ segment ℝ (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val)))
    (tail : p ∈ (F.componentTail c).carrier) : M.cutPieceLabel F covered (Sum.inl e) = c := by
  have in_cap : p ∈ K.footprint := K.convex_projection.segment_subset
    (K.projectedVertex_mem_footprint e.val)
    (K.projectedVertex_mem_footprint (M.parents.parent e.val)) old
  have rim : p ∈ frontier K.footprint :=
    (mem_frontier_iff_notMem_interior in_cap).mpr (F.component_outside c tail)
  have at_parent := M.parent_segment_frontier_endpoint e old rim
  have boundary : C.IsBoundaryVertex Set.univ (M.parents.parent e.val) :=
    (K.projectedVertex_mem_frontier_iff _).mp (at_parent ▸ rim)
  have root : M.parents.root e.val = M.parents.parent e.val :=
    (M.parents.root_eq_of_ancestor (M.parents.ancestor_parent e.val)).trans
      (M.parents.root_of_root ((Set.ext_iff.mp M.roots_eq _).mpr boundary))
  have member : K.projectedVertex (M.parents.root e.val) ∈ (F.componentTail c).carrier := by
    rw [root]
    exact at_parent ▸ tail
  exact F.rimComponent_eq_of_member covered (M.parents.root e.val)
    (M.rootPath_end_boundary e.val) c member

/-- Distinct original trees cannot merge through a skirt component, and independent skirt
components are disjoint. Every geometric contact therefore preserves its component label. -/
theorem cutPiece_labels_compatible (i j : M.ExtendedCutPiece F)
    (meeting : (segment ℝ (M.cutPieceFirst F i) (M.cutPieceLast F i) ∩
      segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j)).Nonempty) :
    M.cutPieceLabel F covered i = M.cutPieceLabel F covered j := by
  obtain ⟨p, first, last⟩ := meeting
  cases i with
  | inl e =>
    cases j with
    | inl f =>
      have roots := M.parent_segments_root_eq_of_intersection e f first last
      exact congrArg (fun w : C.BoundaryVertex Set.univ =>
        F.rimComponent covered w.val w.property)
        (Subtype.ext roots : (⟨M.parents.root e.val, M.rootPath_end_boundary e.val⟩ :
          C.BoundaryVertex Set.univ) = ⟨M.parents.root f.val, M.rootPath_end_boundary f.val⟩)
    | inr c => exact M.parentPiece_label_of_tail_intersection F covered e c first last
  | inr c =>
    cases j with
    | inl e => exact (M.parentPiece_label_of_tail_intersection F covered e c last first).symm
    | inr d =>
      by_contra different
      exact Set.disjoint_left.mp (F.components_disjoint different) first last

end Unfoldings.ConvexRoof.SectorForest
