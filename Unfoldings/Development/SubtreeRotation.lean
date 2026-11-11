module

public import Unfoldings.Development.BoundaryRotations
public import Unfoldings.Development.BankLengths
public import Unfoldings.Complex.SelectedSubtreeAngles
public import Unfoldings.Complex.SubtreeContour
public import Unfoldings.Geometry.CyclicRotations

/-!
# Actual bank rotation around an entire branching subtree

The internal boundary rotations cancel. The two remaining actual parent-seam
banks, directed the same way, differ by the sum of the descendant curvatures.
All bank labels and angles come from the actual original-edge cut forest.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (D : FacewiseDevelopment C (C.selectedRetain S))
  {n : ℕ} (cycle : (C.boundarySystem (C.selectedRetain S)).Chain n)
  (closes : C.boundaryMate (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) cycle.last) = cycle.first)
  (covers : ∀ p, cycle.Visited p)

include roots closes covers in
/-- Prescribed oriented subtree exits determine the actual normalized parent-bank rotation. -/
theorem subtree_bank_rotation_of_exits (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (enter leave : Fin (n + 1)) (different : enter ≠ leave)
    (enters : ¬ C.SubtreeBoundaryInside S cycle e enter ∧
      C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) enter))
    (leaves : C.SubtreeBoundaryInside S cycle e leave ∧
      ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave →
      (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ↔
        C.SubtreeBoundaryInside S cycle e i)) :
    (∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point enter)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side) ∧
    (∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point leave)).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side) ∧
    NormedSpace.normalize (D.boundaryCycleFrame cycle (-D.boundaryRay (cycle.point leave))) =
      polarRay (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) *
        NormedSpace.normalize (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point enter))) := by
  classical
  let L := D.boundaryCycleFrame cycle
  let direction (i : Fin (n + 1)) := NormedSpace.normalize (L (D.boundaryRay (cycle.point i)))
  let turn (i : Fin (n + 1)) :=
    Real.pi - C.totalAngle (C.selectedRetain S)
      (C.boundaryEndVertex (C.selectedRetain S) (cycle.point i))
  let curvature := ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v
  have nonzero (i : Fin (n + 1)) : direction i ≠ 0 := by
    change NormedSpace.normalize (L (D.boundaryRay (cycle.point i))) ≠ 0
    rw [ne_eq, NormedSpace.normalize_eq_zero_iff]
    simpa only [map_zero] using L.injective.ne (D.boundaryRay_ne_zero (cycle.point i))
  have rotation := rotation_of_two_region_exits (finRotate (n + 1))
    (C.SubtreeBoundaryInside S cycle e) direction nonzero turn
    (D.normalized_boundary_step cycle closes) enter leave different enters leaves stable
  have aggregate : (∑ i : Fin (n + 1), if C.SubtreeBoundaryInside S cycle e i then
      C.totalAngle (C.selectedRetain S)
        (C.boundaryEndVertex (C.selectedRetain S) (cycle.point i)) - Real.pi else 0) =
      Real.pi - curvature :=
    (C.sum_boundaryCycle_vertices (C.selectedRetain S) cycle closes covers
      (C.selectedCut_all_vertices_boundary S roots) _).trans
        (C.sum_subtree_boundary_turn S roots cycle closes covers e nonroot)
  have turn_sum : (∑ i, if C.SubtreeBoundaryInside S cycle e i then turn i else 0) =
      curvature - Real.pi := by
    calc
      _ = -(∑ i : Fin (n + 1), if C.SubtreeBoundaryInside S cycle e i then
          C.totalAngle (C.selectedRetain S)
            (C.boundaryEndVertex (C.selectedRetain S) (cycle.point i)) - Real.pi else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [turn]
        split_ifs <;> ring
      _ = _ := by rw [aggregate]; ring
  rw [turn_sum] at rotation
  have entrance := (C.subtreeCrossingBank_iff S roots e nonroot _).mp
    ((C.subtree_boundary_change_iff S cycle closes e enter).mpr (Or.inr ⟨enters.2, enters.1⟩))
  have exit := (C.subtreeCrossingBank_iff S roots e nonroot _).mp
    ((C.subtree_boundary_change_iff S cycle closes e leave).mpr (Or.inl leaves))
  refine ⟨entrance, exit, ?_⟩
  simp only [map_neg, NormedSpace.normalize_neg]
  change -direction leave = polarRay curvature * direction enter
  have half_turn : polarRay (-Real.pi) = -1 := by
    apply Complex.ext <;> simp
  have phase : polarRay (curvature - Real.pi) = -polarRay curvature := by
    rw [sub_eq_add_neg, polarRay_add, half_turn, mul_neg_one]
  rw [rotation, phase]
  ring

include roots closes covers in
/-- The rotation uses the actual two banks of the original parent seam, including all branches. -/
theorem exists_subtree_bank_rotation (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    ∃ enter leave : Fin (n + 1), enter ≠ leave ∧
      (∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side) ∧
      (∃ side, (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side) ∧
      NormedSpace.normalize (D.boundaryCycleFrame cycle (-D.boundaryRay (cycle.point leave))) =
        polarRay (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) *
          NormedSpace.normalize
            (D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point enter))) := by
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots cycle closes covers e nonroot
  obtain ⟨entrance, exit, rotation⟩ :=
    D.subtree_bank_rotation_of_exits S roots cycle closes covers e nonroot
      enter leave different enters leaves stable
  exact ⟨enter, leave, different, entrance, exit, rotation⟩

include roots closes covers in
/-- Prescribed oriented exits give the actual rigid rotation, including bank lengths. -/
theorem subtree_rigid_bank_rotation_of_exits (F : SpatialFolding C)
    (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (enter leave : Fin (n + 1)) (different : enter ≠ leave)
    (enters : ¬ C.SubtreeBoundaryInside S cycle e enter ∧
      C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) enter))
    (leaves : C.SubtreeBoundaryInside S cycle e leave ∧
      ¬ C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave →
      (C.SubtreeBoundaryInside S cycle e (finRotate (n + 1) i) ↔
        C.SubtreeBoundaryInside S cycle e i)) :
    ∃ side : Bool,
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) (!side) ∧
      D.boundaryCycleFrame cycle (-D.boundaryRay (cycle.point leave)) =
        polarRay (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) *
          D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point enter)) := by
  obtain ⟨⟨a, first⟩, ⟨b, last⟩, rotation⟩ :=
    D.subtree_bank_rotation_of_exits S roots cycle closes covers e nonroot
      enter leave different enters leaves stable
  have opposite : b = !a := by
    have distinct : b ≠ a := by
      intro same
      apply different
      exact C.boundaryChain_banks_injective (C.selectedRetain S) cycle
        (first.trans (same ▸ last).symm)
    cases a <;> cases b <;> first | rfl | exact (distinct rfl).elim
  have first_edge := congrArg Subtype.val first
  have last_edge := congrArg Subtype.val last
  change C.germEdge (cycle.point enter).val = C.seamSide (S.edge ⟨e, nonroot⟩) a at first_edge
  change C.germEdge (cycle.point leave).val = C.seamSide (S.edge ⟨e, nonroot⟩) b at last_edge
  have lengths := D.boundaryRay_norm_eq_of_seam F (cycle.point enter) (cycle.point leave)
    (S.edge ⟨e, nonroot⟩) a b first_edge last_edge
  let L := D.boundaryCycleFrame cycle
  let x := L (D.boundaryRay (cycle.point enter))
  let y := L (-D.boundaryRay (cycle.point leave))
  let κ := ∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v
  have same : ‖y‖ = ‖x‖ := by simpa only [y, x, L.norm_map, norm_neg] using lengths.symm
  change NormedSpace.normalize y = polarRay κ * NormedSpace.normalize x at rotation
  refine ⟨a, first, ?_, ?_⟩
  · simpa only [opposite] using last
  · change y = polarRay κ * x
    calc
      y = ‖y‖ • NormedSpace.normalize y := (NormedSpace.norm_smul_normalize _).symm
      _ = ‖x‖ • (polarRay κ * NormedSpace.normalize x) := by rw [same, rotation]
      _ = polarRay κ * (‖x‖ • NormedSpace.normalize x) := by
        simp only [Complex.real_smul]
        ring
      _ = polarRay κ * x := by rw [NormedSpace.norm_smul_normalize]

include roots closes covers in
/-- Equal actual edge lengths upgrade the whole-subtree direction identity to a rigid rotation. -/
theorem exists_subtree_rigid_bank_rotation (F : SpatialFolding C)
    (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots) :
    ∃ enter leave : Fin (n + 1), ∃ side : Bool,
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point enter)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side ∧
      (C.boundaryEndEquiv (C.selectedRetain S) (cycle.point leave)).1 =
        C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) (!side) ∧
      D.boundaryCycleFrame cycle (-D.boundaryRay (cycle.point leave)) =
        polarRay (∑ v ∈ P.descendants e, C.interiorAngularDefect Set.univ v) *
          D.boundaryCycleFrame cycle (D.boundaryRay (cycle.point enter)) := by
  obtain ⟨enter, leave, different, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots cycle closes covers e nonroot
  obtain ⟨side, first, last, rotation⟩ :=
    D.subtree_rigid_bank_rotation_of_exits S roots cycle closes covers F e nonroot
      enter leave different enters leaves stable
  exact ⟨enter, leave, side, first, last, rotation⟩

end Unfoldings.FacewiseDevelopment
