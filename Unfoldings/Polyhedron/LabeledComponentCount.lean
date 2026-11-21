module

public import Unfoldings.Polyhedron.LabeledCutConnectivity
public import Unfoldings.Polyhedron.GaussianSideDisjoint
public import Unfoldings.Combinatorics.ComponentEulerAccounting

/-! Euler accounting for labels whose original face components are disks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open Classical in
/-- The original seams incident to a vertex of the triangulation. -/
def incidentSeams (p : C.Vertex Set.univ) : Finset C.Seam :=
  Finset.univ.filter fun s => p = C.seamVertex s false ∨ p = C.seamVertex s true

open Classical in
/-- The number of incident seams joining triangles with different labels. -/
def labelCutDegree {L : Type*} (label : Face → L) (p : C.Vertex Set.univ) : ℕ :=
  ((incidentSeams p).filter fun s => label (C.left s).face ≠ label (C.right s).face).card

theorem labelCutVertex_iff_degree_ne_zero {L : Type*} (label : Face → L) (p : C.Vertex Set.univ) :
    labelCutVertex label p ↔ labelCutDegree label p ≠ 0 := by
  classical
  rw [labelCutDegree, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  constructor
  · rintro ⟨s, b, cut, eq⟩
    refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, cut⟩⟩
    cases b
    · exact Or.inl eq
    · exact Or.inr eq
  · rintro ⟨s, h⟩
    obtain ⟨side, cut⟩ := Finset.mem_filter.mp h
    rcases (Finset.mem_filter.mp side).2 with eq | eq
    · exact ⟨s, false, cut, eq⟩
    · exact ⟨s, true, cut, eq⟩

open Classical in
include P in
/-- The exact Gaussian charge formula before removing any flat subdivision
vertices. The disk hypothesis applies to the original uncut face components. -/
theorem labeled_component_count_eq_two_add_sum_vertex_charges {L : Type*} (label : Face → L)
    (disks : ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.RestrictionIsDisk c.supp) :
    (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) =
      2 + ∑ p : C.Vertex Set.univ, componentCharge (labelCutDegree label p) := by
  let changed (s : C.Seam) := label (C.left s).face ≠ label (C.right s).face
  let inactive (p : C.Vertex Set.univ) := labelCutDegree label p = 0
  have euler := P.triangulation_euler
  have formula := P.labeled_components_eq_cut_cycle_rank label
  rw [P.card_labelCutGraph_components_of_disks label disks] at formula
  have inactive_eq : {p : C.Vertex Set.univ | ¬ labelCutVertex label p} = {p | inactive p} := by
    ext p
    change ¬ labelCutVertex label p ↔ labelCutDegree label p = 0
    rw [labelCutVertex_iff_degree_ne_zero, not_ne_iff]
  change _ + _ = 1 + Fintype.card {s // changed s} +
    (1 + Nat.card ↑{p : C.Vertex Set.univ | ¬ labelCutVertex label p}) at formula
  rw [inactive_eq] at formula
  change _ + _ = 1 + Fintype.card {s // changed s} +
    (1 + Nat.card {p // inactive p}) at formula
  have cut_card : Fintype.card {s // changed s} = (Finset.univ.filter changed).card :=
    Fintype.card_subtype changed
  have inactive_card : Nat.card {p // inactive p} = (Finset.univ.filter inactive).card := by
    rw [Nat.card_eq_fintype_card (α := {p // inactive p})]
    exact Fintype.card_subtype inactive
  rw [cut_card, inactive_card] at formula
  have cut_split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset C.Seam))
    changed
  rw [Finset.card_univ] at cut_split
  have twice (s : C.Seam) :
      (Finset.univ.filter fun p : C.Vertex Set.univ => s ∈ incidentSeams p).card = 2 := by
    have endpoints :
        (Finset.univ.filter fun p : C.Vertex Set.univ => s ∈ incidentSeams p) =
          {C.seamVertex s false, C.seamVertex s true} := by
      ext p
      simp [incidentSeams]
    have distinct : C.seamVertex s false ≠ C.seamVertex s true :=
      fun h => gaussianSiteOfVertex_seam_ne (F := F) s
        (congrArg (fun v => (F.gaussianSiteOfVertex v : Space)) h)
    rw [endpoints, Finset.card_pair distinct]
  apply component_count_eq_two_add_sum_charges incidentSeams changed (Fintype.card Face)
  · omega
  · change (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℤ) =
      (Fintype.card Face : ℤ) - ((Finset.univ.filter fun e => ¬ changed e).card : ℤ) +
        (((Finset.univ : Finset (C.Vertex Set.univ)).filter inactive).card : ℤ)
    omega
  · exact twice

end Unfoldings.SpatialFolding.ConvexBoundary
