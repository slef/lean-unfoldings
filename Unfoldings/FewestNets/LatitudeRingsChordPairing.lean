module

public import Unfoldings.FewestNets.LatitudeRingsRowPairing
public import Unfoldings.FewestNets.LatitudeRingsOrientation
public import Unfoldings.Geometry.RadialTriangleOrientation

/-! The actual latitude mesh pairs every side, with the opposite orientations at each seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real Module

variable (G : LatitudeRings)

local notation "Step" j => sweepOrder (rowSize G (Fin.val j)) (rowSize G (Fin.val j + 1))

/-- Cyclic successor within one strip or one of the polar fans. -/
def chordFaceNext : Equiv.Perm (ChordFace G) :=
  Equiv.sumCongr (finRotate (rowSize G 0))
    (Equiv.sumCongr (Equiv.sigmaCongrRight (fun _ => finRotate _))
      (finRotate (rowSize G (stripCount G))))

/-- The side coming from the previous triangle in a strip or fan. -/
def chordEntrySlot : ChordFace G → Fin 3
  | .inl _ => 1
  | .inr (.inl ⟨j, i⟩) => entrySlot G j.val (Step j) i
  | .inr (.inr _) => 2

/-- The side departing to the next triangle in a strip or fan. -/
def chordExitSlot : ChordFace G → Fin 3
  | .inl _ => 2
  | .inr (.inl ⟨j, i⟩) => exitSlot G j.val (Step j) i
  | .inr (.inr _) => 1

theorem chordSideSlots_distinct (i : ChordFace G) :
    chordEntrySlot G i ≠ chordExitSlot G i ∧
    chordEntrySlot G i ≠ ringSlot i ∧ chordExitSlot G i ≠ ringSlot i := by
  rcases i with _ | ⟨j, i⟩ | _
  · change (1 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 0 ∧ (2 : Fin 3) ≠ 0
    decide
  · exact sweep_slots_distinct G j.val (Step j) i
  · change (2 : Fin 3) ≠ 1 ∧ (2 : Fin 3) ≠ 0 ∧ (1 : Fin 3) ≠ 0
    decide

private theorem chordSideSlots_cover (i : ChordFace G) (e : Fin 3) :
    e = ringSlot i ∨ e = chordEntrySlot G i ∨ e = chordExitSlot G i := by
  rcases i with _ | ⟨j, i⟩ | _
  · change e = 0 ∨ e = 1 ∨ e = 2
    fin_cases e <;> decide
  · let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
    change e = 2 ∨ e = entrySlot G j.val step i ∨ e = exitSlot G j.val step i
    unfold entrySlot exitSlot
    cases pick : step i
    · change e = 2 ∨ e = 1 ∨ e = 0
      fin_cases e <;> decide
    · change e = 2 ∨ e = 0 ∨ e = 1
      fin_cases e <;> decide
  · change e = 0 ∨ e = 2 ∨ e = 1
    fin_cases e <;> decide

private theorem rowSite_rotate (j : ℕ) (b : Fin (rowSize G j)) :
    rowSite G j (finRotate (rowSize G j) b).val = rowSite G j (b.val + 1) := by
  have positive : 0 < rowSize G j := Nat.zero_lt_of_lt b.isLt
  let : NeZero (rowSize G j) := ⟨positive.ne'⟩
  have rotate_val : (finRotate (rowSize G j) b).val = (b.val + 1) % rowSize G j := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [rotate_val, rowSite_mod G j _ positive]

/-- Following a strip or fan, the two incident triangles traverse each shared side oppositely. -/
theorem chordFaceNext_opposite {G : LatitudeRings} (hG : Admissible G)
    (i : ChordFace G) :
    orientedChordEdge (chordVertices G (chordFaceNext G i))
      (chordEntrySlot G (chordFaceNext G i)) =
      (orientedChordEdge (chordVertices G i) (chordExitSlot G i)).swap := by
  rcases i with b | ⟨j, i⟩ | b
  · change (rowSite G 0 (finRotate (rowSize G 0) b).val, latitudeSite 0 0) =
      (rowSite G 0 (b.val + 1), latitudeSite 0 0)
    rw [rowSite_rotate]
  · exact sweep_next_opposite_slots G j.val (sweepOrder _ _) (sweepOrder_sorted _ _)
      (rowSize_pos hG j.isLt.le)
      (rowSize_pos hG (Nat.succ_le_of_lt j.isLt)) i
  · let last := stripCount G
    change (latitudeSite π 0, rowSite G last (finRotate (rowSize G last) b).val) =
      (latitudeSite π 0, rowSite G last (b.val + 1))
    rw [rowSite_rotate]

/-- The opposite triangle side paired to a side of the actual chord mesh. -/
def chordSideMate (e : ChordFace G × Fin 3) : ChordFace G × Fin 3 :=
  if e.2 = ringSlot e.1 then (ringFaceMate G e.1, ringSlot (ringFaceMate G e.1))
  else if e.2 = chordEntrySlot G e.1 then
    let previous := (chordFaceNext G).symm e.1
    (previous, chordExitSlot G previous)
  else
    let next := chordFaceNext G e.1
    (next, chordEntrySlot G next)

private theorem chordSideMate_ring (i : ChordFace G) :
    chordSideMate G (i, ringSlot i) = (ringFaceMate G i, ringSlot (ringFaceMate G i)) := by
  simp [chordSideMate]

private theorem chordSideMate_entry (i : ChordFace G) :
    chordSideMate G (i, chordEntrySlot G i) =
      ((chordFaceNext G).symm i, chordExitSlot G ((chordFaceNext G).symm i)) := by
  simp [chordSideMate, (chordSideSlots_distinct G i).2.1]

private theorem chordSideMate_exit (i : ChordFace G) :
    chordSideMate G (i, chordExitSlot G i) =
      (chordFaceNext G i, chordEntrySlot G (chordFaceNext G i)) := by
  have slots := chordSideSlots_distinct G i
  simp [chordSideMate, slots.1.symm, slots.2.2]

theorem chordSideMate_involutive : Function.Involutive (chordSideMate G) := by
  rintro ⟨i, e⟩
  rcases chordSideSlots_cover G i e with rfl | rfl | rfl
  · rw [chordSideMate_ring, chordSideMate_ring, ringFaceMate_involutive G i]
  · rw [chordSideMate_entry, chordSideMate_exit, Equiv.apply_symm_apply]
  · rw [chordSideMate_exit, chordSideMate_entry, Equiv.symm_apply_apply]

/-- Both incidence labels name the identical physical edge with reversed endpoints. -/
theorem chordSideMate_opposite {G : LatitudeRings} (hG : Admissible G)
    (e : ChordFace G × Fin 3) :
    orientedChordEdge (chordVertices G (chordSideMate G e).1) (chordSideMate G e).2 =
      (orientedChordEdge (chordVertices G e.1) e.2).swap := by
  obtain ⟨i, e⟩ := e
  rcases chordSideSlots_cover G i e with rfl | rfl | rfl
  · rw [chordSideMate_ring]
    exact ringFaceMate_opposite G i
  · rw [chordSideMate_entry]
    have pair := chordFaceNext_opposite hG ((chordFaceNext G).symm i)
    rw [Equiv.apply_symm_apply] at pair
    exact (congrArg Prod.swap pair).symm
  · rw [chordSideMate_exit]
    exact chordFaceNext_opposite hG i

variable {G}

/-- The actual oriented bases, with no arbitrary choices of vertex order. -/
def chordBasis (hG : Oriented G) (i : ChordFace G) :
    Basis (Fin 3) ℝ Space :=
  Classical.choose (exists_chordBasis hG i)

@[simp] theorem chordBasis_apply (hG : Oriented G) (i : ChordFace G)
    (k : Fin 3) : chordBasis hG i k = chordVertices G i k :=
  congrFun (Classical.choose_spec (exists_chordBasis hG i)) k

/-- The paired sides preserve their open edges and have oppositely signed transverse coordinates. -/
theorem chordBasis_edge_pair (hG : Oriented G)
    (e : ChordFace G × Fin 3) :
    let b := chordBasis hG
    let f := chordSideMate G e
    (∀ p, OnOpenRadialEdge (b e.1) e.2 p → OnOpenRadialEdge (b f.1) f.2 p) ∧
      ∃ c < (0 : ℝ), ∀ q, (b e.1).coord e.2 q = c * (b f.1).coord f.2 q := by
  let b := chordBasis hG
  let f := chordSideMate G e
  let std := OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ)
  have negative (i : ChordFace G) : std.det (b i) < 0 := by
    rw [show (b i : Fin 3 → Space) = chordVertices G i from funext (chordBasis_apply hG i)]
    exact chordVertices_det_neg hG i
  have pair := chordSideMate_opposite hG.toAdmissible e
  have first := (congrArg Prod.snd pair).symm
  have last := (congrArg Prod.fst pair).symm
  change chordVertices G e.1 (finRotate 3 e.2) =
    chordVertices G f.1 (finRotate 3 (finRotate 3 f.2)) at first
  change chordVertices G e.1 (finRotate 3 (finRotate 3 e.2)) =
    chordVertices G f.1 (finRotate 3 f.2) at last
  apply radialEdge_opposite_of_consistent_orientation (b e.1) (b f.1) e.2 f.2
    (negative e.1) (negative f.1)
  · exact (chordBasis_apply hG _ _).trans
      (first.trans (chordBasis_apply hG _ _).symm)
  · exact (chordBasis_apply hG _ _).trans
      (last.trans (chordBasis_apply hG _ _).symm)

end Unfoldings.FewestNets.LatitudeRings
