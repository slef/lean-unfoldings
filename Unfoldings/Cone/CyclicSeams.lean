module

public import Unfoldings.Cone.LinkComparison
public import Unfoldings.Topology.ChainPairings

/-!
# Closing the outer banks of an actual cyclic link

Every actual pairing is consecutive or closes the two outer banks. The
closing radial identification is constructed from its original seam at every
nonnegative radius, without requiring a planar full-turn hypothesis.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentSeam_cyclic_cases {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (s : C.TangentSeam retain v) :
    (∃ k : Fin n, C.tangentSourceGerm retain v s = C.turnGerm (chain.point k.castSucc).val ∧
      C.tangentTargetGerm retain v s = (chain.point k.succ).val) ∨
    (∃ k : Fin n, C.tangentSourceGerm retain v s = (chain.point k.succ).val ∧
      C.tangentTargetGerm retain v s = C.turnGerm (chain.point k.castSucc).val) ∨
    (C.tangentSourceGerm retain v s = C.turnGerm chain.last.val ∧
      C.tangentTargetGerm retain v s = chain.first.val) ∨
    (C.tangentSourceGerm retain v s = chain.first.val ∧
      C.tangentTargetGerm retain v s = C.turnGerm chain.last.val) := by
  let p : C.LinkGerm retain v := ⟨C.tangentSourceGerm retain v s, s.property.2⟩
  let q : C.LinkGerm retain v :=
    ⟨C.tangentTargetGerm retain v s, (C.tangentRight retain v s).property⟩
  have paired : C.linkMate retain v p = q := by
    apply Subtype.ext
    exact C.mateGerm_of_crossing (C.tangentSeam_crosses retain v s)
  have different : p ≠ q := by
    intro equal
    exact GermCrosses.ne C (C.tangentSeam_crosses retain v s) (congrArg Subtype.val equal)
  have start : C.linkMate retain v chain.first = C.linkTurn retain v chain.last := by
    rw [← closes, C.linkMate_involutive]
  rcases chain.pairing_cases (Or.inl start) (Or.inl closes) (covers p) paired different with
    ⟨k, source, target⟩ | ⟨k, source, target⟩ | ⟨source, target⟩ | ⟨source, target⟩
  · exact Or.inl ⟨k, congrArg Subtype.val source, congrArg Subtype.val target⟩
  · exact Or.inr (Or.inl ⟨k, congrArg Subtype.val source, congrArg Subtype.val target⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨congrArg Subtype.val source, congrArg Subtype.val target⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨congrArg Subtype.val source, congrArg Subtype.val target⟩))

/-- An actual directed pairing identifies its corresponding angular banks in the tangent fan. -/
theorem linkCellToTangent_pair {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (i j : Fin (n + 1))
    (paired : C.linkMate retain v (C.linkTurn retain v (chain.point i)) = chain.point j)
    (different : chain.point j ≠ C.linkTurn retain v (chain.point i)) (r : ℝ≥0) :
    C.linkCellToTangent retain v chain i ((C.linkAngularFan retain v chain).finish i r) =
      C.linkCellToTangent retain v chain j ((C.linkAngularFan retain v chain).start j r) := by
  obtain ⟨s, source, target⟩ := C.exists_tangentSeam_of_link_next_germs retain v
    (chain.point i) (chain.point j) paired different
  have source_corner : (C.tangentLeft retain v s).val = (chain.point i).val.1 := by
    have corners := congrArg (fun p : C.Germ => p.1) source
    exact corners
  have target_corner : (C.tangentRight retain v s).val = (chain.point j).val.1 :=
    congrArg Prod.fst target
  have turned : C.turnGerm (C.tangentSourceGerm retain v s) = (chain.point i).val :=
    (congrArg C.turnGerm source).trans (C.turnGerm_involutive _)
  have left_coordinates := C.germFrame_seam_left retain v s r
  rw [turned] at left_coordinates
  have angle := congrArg (fun c : C.Corner => (C.triangle c.1).cornerAngle c.2) source_corner
  change (C.triangle (C.tangentLeft retain v s).val.1).cornerAngle
    (C.tangentLeft retain v s).val.2 = (C.linkAngularFan retain v chain).angle i at angle
  rw [angle] at left_coordinates
  have right_coordinates := C.germFrame_seam_right retain v s r
  rw [target] at right_coordinates
  calc
    _ = C.tangentFaceMap retain v (C.tangentLeft retain v s)
        (C.tangentSeamPointLeft retain v s r) :=
      C.linkCellToTangent_of_coordinates retain v chain i _ _
        (C.tangentSeamPointLeft retain v s r) source_corner left_coordinates
    _ = C.tangentFaceMap retain v (C.tangentRight retain v s)
        (C.tangentSeamPointRight retain v s r) :=
      MetricGluing.point_eq_of_glue (C.TangentCell retain v)
        (C.tangentSeamPoints_glue retain v s r)
    _ = _ := (C.linkCellToTangent_of_coordinates retain v chain j _ _
      (C.tangentSeamPointRight retain v s r) target_corner right_coordinates).symm

theorem linkCellToTangent_outer_banks {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first) (r : ℝ≥0) :
    C.linkCellToTangent retain v chain (Fin.last n)
      ((C.linkAngularFan retain v chain).finish (Fin.last n) r) =
    C.linkCellToTangent retain v chain 0 ((C.linkAngularFan retain v chain).start 0 r) :=
  C.linkCellToTangent_pair retain v chain (Fin.last n) 0 closes
    (chain.disjoint 0 (Fin.last n)) r

theorem angularToTangent_outer_banks {n : ℕ} (chain : (C.linkSystem retain v).Chain n)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first) (r : ℝ≥0) :
    C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap (Fin.last n)
      ((C.linkAngularFan retain v chain).finish (Fin.last n) r)) =
    C.angularToTangent retain v chain ((C.linkAngularFan retain v chain).faceMap 0
      ((C.linkAngularFan retain v chain).start 0 r)) := by
  rw [C.angularToTangent_faceMap, C.angularToTangent_faceMap]
  exact C.linkCellToTangent_outer_banks retain v chain closes r

end Unfoldings.TriangleComplex
