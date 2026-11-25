module

public import Unfoldings.FewestNets.GaussianMarkedSides
public import Unfoldings.FewestNets.GaussianCentralCharge

/-! Translate the signed original-seam count to the genuine oriented Gaussian cycle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.SingleCellCharge

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- Full selection of an original vertex's link is equivalent to selection of
all original face corners at that vertex. -/
theorem fullSelectedLink_iff_all_incident_faces (U : Set Face) (a : C.Vertex Set.univ) :
    fullSelectedLink U a ↔ ∀ f j, C.vertexOfCorner Set.univ (f, j) = a → f ∈ U := by
  classical
  constructor
  · intro full f j at_a
    let p : C.LinkGerm Set.univ a := ⟨((f, j), false), at_a⟩
    let s := P.germSeam p.val
    have selected := full s (P.germSeam_mem_incidentSeams p)
    obtain ⟨b, on_side⟩ := P.exists_germSeam_side p.val
    have same := congrArg (fun p : C.Germ => p.1.1) on_side
    change f = (C.seamSide s b).face at same
    cases b
    · exact same ▸ selected.1
    · exact same ▸ selected.2
  · intro all s member
    have endpoint : ∃ b, C.seamVertex s b = a := by
      rcases (Finset.mem_filter.mp member).2 with first | last
      · exact ⟨false, first.symm⟩
      · exact ⟨true, last.symm⟩
    obtain ⟨b, at_a⟩ := endpoint
    let p := C.germOfEndpoint (C.left s) b
    let q := C.germOfEndpoint (C.right s) (C.acrossEndpoint s false b)
    have across : C.GermCrosses Set.univ p q := ⟨s, Set.mem_univ s, false, b, rfl, rfl⟩
    have at_q : C.vertexOfCorner Set.univ q.1 = a := by
      rw [← C.mateGerm_of_crossing across, C.mateGerm_vertex_eq]
      exact at_a
    exact ⟨all p.1.1 p.1.2 at_a, all q.1.1 q.1.2 at_q⟩

variable {a : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)
  (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
  (covers : ∀ p, c.Visited p)
  {m : ℕ} (count : (cyclicRunStarts (linkNormals N c)).card = m + 1)

open Classical in
include P closes covers in
set_option maxHeartbeats 1000000 in
/-- The signed charge uses the exact oriented cycle after compressing flat seams.
The two marked sides retain the endpoints of their original physical seams. -/
theorem gaussianSignedCharge_eq_cycleCharge (label : Space → Bool) (first second : Fin (m + 1)) :
    let normal := compressedLinkNormal N c count
    let next := finRotate (m + 1)
    let e := P.runStartGaussianSeamEquiv N c closes covers count
    gaussianSignedCharge N label a (e (next first)).val (e (next second)).val =
      cycleCharge (label ∘ normal) first second := by
  let normal := compressedLinkNormal N c count
  let next := finRotate (m + 1)
  let e := P.runStartGaussianSeamEquiv N c closes covers count
  let seam (i : Fin (m + 1)) := (e (next i)).val
  let side := seamMembership N label
  let cost := crossing ∘ side
  let on_cycle (i : Fin (m + 1)) := (label (normal i), label (normal (next i)))
  have actual (i : Fin (m + 1)) : side (seam i) = on_cycle i ∨
      side (seam i) = (on_cycle i).swap := by
    have ends := P.compressedLinkNormal_arcEnds N c closes covers count (next i)
    change HasGaussianArcEnds N (seam i) (normal (next.symm (next i))) (normal (next i)) at ends
    rw [next.symm_apply_apply] at ends
    rcases ends with ⟨left, right⟩ | ⟨left, right⟩
    · left
      change (label (N.normal (C.left (seam i)).face), label (N.normal (C.right (seam i)).face)) = _
      rw [left, right]
    · right
      change (label (N.normal (C.left (seam i)).face), label (N.normal (C.right (seam i)).face)) = _
      rw [left, right]
      rfl
  have side_cost (i : Fin (m + 1)) : cost (seam i) = crossing (on_cycle i) := by
    change crossing (side (seam i)) = _
    rcases actual i with eq | eq
    · rw [eq]
    · rw [eq]
      simp only [crossing, Prod.fst_swap, Prod.snd_swap, eq_comm]
  have marked (i : Fin (m + 1)) : endpoints (side (seam i)) = endpoints (on_cycle i) := by
    rcases actual i with eq | eq
    · rw [eq]
    · rw [eq]
      simp only [endpoints, Prod.fst_swap, Prod.snd_swap, add_comm]
  let embedding : Fin (m + 1) ↪ C.Seam :=
    ⟨seam, Subtype.val_injective.comp (e.injective.comp next.injective)⟩
  have map_all : Finset.univ.map embedding = gaussianArcSeams N a := by
    ext s
    constructor
    · intro member
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp member
      exact (e (next i)).property
    · intro member
      obtain ⟨i, equal⟩ := (next.trans e).surjective ⟨s, member⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val equal⟩
  have change_sum : (∑ s ∈ incidentSeams a, cost s) = ∑ i, crossing (on_cycle i) := by
    calc
      _ = ∑ s ∈ gaussianArcSeams N a, cost s := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro s inside missing
        have same : N.normal (C.left s).face = N.normal (C.right s).face := by
          by_contra different
          exact missing (Finset.mem_filter.mpr ⟨inside, different⟩)
        simp only [cost, Function.comp_apply, side, seamMembership, same, crossing, ite_true]
      _ = _ := by
        rw [← map_all, Finset.sum_map]
        exact Finset.sum_congr rfl (fun i _ => side_cost i)
  let U : Set Face := {f | label (N.normal f) = true}
  have range : Set.range normal =
      {x | ∃ (f : Face) (j : Fin 3), C.vertexOfCorner Set.univ (f, j) = a ∧ N.normal f = x} :=
    range_compressed_linkNormals N c covers count
  have full : fullSelectedLink U a ↔ ∀ i, (label ∘ normal) i = true := by
    rw [P.fullSelectedLink_iff_all_incident_faces]
    constructor
    · intro all i
      have mem : normal i ∈ Set.range normal := ⟨i, rfl⟩
      rw [range] at mem
      obtain ⟨f, j, at_a, same⟩ := mem
      change label (normal i) = true
      rw [← same]
      exact all f j at_a
    · intro all f j at_a
      have mem := range.symm ▸ (show N.normal f ∈ {x | ∃ (f : Face) (j : Fin 3),
          C.vertexOfCorner Set.univ (f, j) = a ∧ N.normal f = x} from ⟨f, j, at_a, rfl⟩)
      obtain ⟨i, same⟩ := mem
      change label (N.normal f) = true
      rw [← same]
      exact all i
  have flags : decide (fullSelectedLink U a) = decide (∀ i, (label ∘ normal) i = true) := by
    by_cases h : fullSelectedLink U a
    · simp only [decide_eq_true h, decide_eq_true (full.mp h)]
    · simp only [decide_eq_false h, decide_eq_false (mt full.mpr h)]
  change charge (∑ s ∈ incidentSeams a, cost s) (side (seam first)) (side (seam second))
      (decide (fullSelectedLink U a)) =
    charge (∑ i, crossing (on_cycle i)) (on_cycle first) (on_cycle second)
      (decide (∀ i, (label ∘ normal) i = true))
  rw [change_sum, flags]
  simp only [charge, marked]

end Unfoldings.SpatialFolding.ConvexBoundary
