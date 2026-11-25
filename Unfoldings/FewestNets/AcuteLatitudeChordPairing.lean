module

public import Unfoldings.FewestNets.AcuteLatitudeRingPairing
public import Unfoldings.FewestNets.LatitudeChordOrientation
public import Unfoldings.Geometry.RadialTriangleOrientation

/-! The actual latitude mesh pairs every side, with the opposite orientations at each seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Module

variable (a : ℝ)

local notation "Step" j => sweepOrder (rowSize a (Fin.val j)) (rowSize a (Fin.val j + 1))

/-- Cyclic successor within one strip or one of the polar fans. -/
def chordFaceNext : Equiv.Perm (ChordFace a) :=
  Equiv.sumCongr (finRotate (rowSize a 0))
    (Equiv.sumCongr (Equiv.sigmaCongrRight (fun _ => finRotate _))
      (finRotate (rowSize a (stripCount a))))

/-- The side coming from the previous triangle in a strip or fan. -/
def chordEntrySlot : ChordFace a → Fin 3
  | .inl _ => 1
  | .inr (.inl ⟨j, i⟩) => entrySlot a j.val (Step j) i
  | .inr (.inr _) => 2

/-- The side departing to the next triangle in a strip or fan. -/
def chordExitSlot : ChordFace a → Fin 3
  | .inl _ => 2
  | .inr (.inl ⟨j, i⟩) => exitSlot a j.val (Step j) i
  | .inr (.inr _) => 1

theorem chordSideSlots_distinct (i : ChordFace a) :
    chordEntrySlot a i ≠ chordExitSlot a i ∧
    chordEntrySlot a i ≠ ringSlot i ∧ chordExitSlot a i ≠ ringSlot i := by
  rcases i with _ | ⟨j, i⟩ | _
  · change (1 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 0 ∧ (2 : Fin 3) ≠ 0
    decide
  · exact sweep_slots_distinct a j.val (Step j) i
  · change (2 : Fin 3) ≠ 1 ∧ (2 : Fin 3) ≠ 0 ∧ (1 : Fin 3) ≠ 0
    decide

private theorem chordSideSlots_cover (i : ChordFace a) (e : Fin 3) :
    e = ringSlot i ∨ e = chordEntrySlot a i ∨ e = chordExitSlot a i := by
  rcases i with _ | ⟨j, i⟩ | _
  · change e = 0 ∨ e = 1 ∨ e = 2
    fin_cases e <;> decide
  · let step := sweepOrder (rowSize a j.val) (rowSize a (j.val + 1))
    change e = 2 ∨ e = entrySlot a j.val step i ∨ e = exitSlot a j.val step i
    unfold entrySlot exitSlot
    cases pick : step i
    · change e = 2 ∨ e = 1 ∨ e = 0
      fin_cases e <;> decide
    · change e = 2 ∨ e = 0 ∨ e = 1
      fin_cases e <;> decide
  · change e = 0 ∨ e = 2 ∨ e = 1
    fin_cases e <;> decide

private theorem rowSite_rotate (j : ℕ) (b : Fin (rowSize a j)) :
    rowSite a j (finRotate (rowSize a j) b).val = rowSite a j (b.val + 1) := by
  have positive : 0 < rowSize a j := Nat.zero_lt_of_lt b.isLt
  let : NeZero (rowSize a j) := ⟨positive.ne'⟩
  have rotate_val : (finRotate (rowSize a j) b).val = (b.val + 1) % rowSize a j := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [rotate_val, rowSite_mod a j _ positive]

/-- Following a strip or fan, the two incident triangles traverse each shared side oppositely. -/
theorem chordFaceNext_opposite {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : ChordFace a) :
    orientedChordEdge (chordVertices a (chordFaceNext a i))
      (chordEntrySlot a (chordFaceNext a i)) =
      (orientedChordEdge (chordVertices a i) (chordExitSlot a i)).swap := by
  rcases i with b | ⟨j, i⟩ | b
  · change (rowSite a 0 (finRotate (rowSize a 0) b).val, latitudeSite 0 0) =
      (rowSite a 0 (b.val + 1), latitudeSite 0 0)
    rw [rowSite_rotate]
  · exact sweep_next_opposite_slots a j.val (sweepOrder _ _) (sweepOrder_sorted _ _)
      (rowSize_pos positive small j.isLt.le)
      (rowSize_pos positive small (Nat.succ_le_of_lt j.isLt)) i
  · let last := stripCount a
    change (latitudeSite π 0, rowSite a last (finRotate (rowSize a last) b).val) =
      (latitudeSite π 0, rowSite a last (b.val + 1))
    rw [rowSite_rotate]

/-- The opposite triangle side paired to a side of the actual chord mesh. -/
def chordSideMate (e : ChordFace a × Fin 3) : ChordFace a × Fin 3 :=
  if e.2 = ringSlot e.1 then (ringFaceMate a e.1, ringSlot (ringFaceMate a e.1))
  else if e.2 = chordEntrySlot a e.1 then
    let previous := (chordFaceNext a).symm e.1
    (previous, chordExitSlot a previous)
  else
    let next := chordFaceNext a e.1
    (next, chordEntrySlot a next)

private theorem chordSideMate_ring (i : ChordFace a) :
    chordSideMate a (i, ringSlot i) = (ringFaceMate a i, ringSlot (ringFaceMate a i)) := by
  simp [chordSideMate]

private theorem chordSideMate_entry (i : ChordFace a) :
    chordSideMate a (i, chordEntrySlot a i) =
      ((chordFaceNext a).symm i, chordExitSlot a ((chordFaceNext a).symm i)) := by
  simp [chordSideMate, (chordSideSlots_distinct a i).2.1]

private theorem chordSideMate_exit (i : ChordFace a) :
    chordSideMate a (i, chordExitSlot a i) =
      (chordFaceNext a i, chordEntrySlot a (chordFaceNext a i)) := by
  have slots := chordSideSlots_distinct a i
  simp [chordSideMate, slots.1.symm, slots.2.2]

theorem chordSideMate_involutive : Function.Involutive (chordSideMate a) := by
  rintro ⟨i, e⟩
  rcases chordSideSlots_cover a i e with rfl | rfl | rfl
  · rw [chordSideMate_ring, chordSideMate_ring, ringFaceMate_involutive a i]
  · rw [chordSideMate_entry, chordSideMate_exit, Equiv.apply_symm_apply]
  · rw [chordSideMate_exit, chordSideMate_entry, Equiv.symm_apply_apply]

/-- Both incidence labels name the identical physical edge with reversed endpoints. -/
theorem chordSideMate_opposite {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (e : ChordFace a × Fin 3) :
    orientedChordEdge (chordVertices a (chordSideMate a e).1) (chordSideMate a e).2 =
      (orientedChordEdge (chordVertices a e.1) e.2).swap := by
  obtain ⟨i, e⟩ := e
  rcases chordSideSlots_cover a i e with rfl | rfl | rfl
  · rw [chordSideMate_ring]
    exact ringFaceMate_opposite a i
  · rw [chordSideMate_entry]
    have pair := chordFaceNext_opposite positive small ((chordFaceNext a).symm i)
    rw [Equiv.apply_symm_apply] at pair
    exact (congrArg Prod.swap pair).symm
  · rw [chordSideMate_exit]
    exact chordFaceNext_opposite positive small i

variable {a}

/-- The actual oriented bases, with no arbitrary choices of vertex order. -/
def chordBasis (positive : 0 < a) (small : a ≤ π / 6) (i : ChordFace a) :
    Basis (Fin 3) ℝ Space :=
  Classical.choose (exists_chordBasis positive small i)

@[simp] theorem chordBasis_apply (positive : 0 < a) (small : a ≤ π / 6) (i : ChordFace a)
    (k : Fin 3) : chordBasis positive small i k = chordVertices a i k :=
  congrFun (Classical.choose_spec (exists_chordBasis positive small i)) k

/-- The paired sides preserve their open edges and have oppositely signed transverse coordinates. -/
theorem chordBasis_edge_pair (positive : 0 < a) (small : a ≤ π / 6)
    (e : ChordFace a × Fin 3) :
    let b := chordBasis positive small
    let f := chordSideMate a e
    (∀ p, OnOpenRadialEdge (b e.1) e.2 p → OnOpenRadialEdge (b f.1) f.2 p) ∧
      ∃ c < (0 : ℝ), ∀ q, (b e.1).coord e.2 q = c * (b f.1).coord f.2 q := by
  let b := chordBasis positive small
  let f := chordSideMate a e
  let std := OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)
  have negative (i : ChordFace a) : std.det (b i) < 0 := by
    rw [show (b i : Fin 3 → Space) = chordVertices a i from funext (chordBasis_apply positive small i)]
    exact chordVertices_det_neg positive small i
  have pair := chordSideMate_opposite positive small e
  have first := (congrArg Prod.snd pair).symm
  have last := (congrArg Prod.fst pair).symm
  change chordVertices a e.1 (finRotate 3 e.2) =
    chordVertices a f.1 (finRotate 3 (finRotate 3 f.2)) at first
  change chordVertices a e.1 (finRotate 3 (finRotate 3 e.2)) =
    chordVertices a f.1 (finRotate 3 f.2) at last
  apply radialEdge_opposite_of_consistent_orientation (b e.1) (b f.1) e.2 f.2
    (negative e.1) (negative f.1)
  · exact (chordBasis_apply positive small _ _).trans
      (first.trans (chordBasis_apply positive small _ _).symm)
  · exact (chordBasis_apply positive small _ _).trans
      (last.trans (chordBasis_apply positive small _ _).symm)

end Unfoldings.FewestNets.AcuteLatitudeGrid
