module

public import Unfoldings.FewestNets.LatitudeSweepEdges
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Consecutive triangles pair the literal cross-row edges, including at the repeated meridian. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

variable (a : ℝ) (j : ℕ)
  (step : Fin (rowSize a j + rowSize a (j + 1)) ≃
    Fin (rowSize a j) ⊕ Fin (rowSize a (j + 1)))

local notation "m" => rowSize a j
local notation "n" => rowSize a (j + 1)
local notation "Sweep" => latitudeSweepCrossSites a j step
local notation "Tri" => latitudeSweepChordVertices a j step

/-- The cyclic edge opposite vertex `k`, in its actual traversal order. -/
def orientedChordEdge (v : Fin 3 → Space) (k : Fin 3) : Space × Space :=
  (v (finRotate 3 k), v (finRotate 3 (finRotate 3 k)))

/-- The entering side of the step is the one opposite the newly added vertex. -/
def entrySlot (i : Fin (m + n)) : Fin 3 :=
  match step i with
  | .inl _ => 1
  | .inr _ => 0

/-- The leaving side of the step is the one opposite the replaced vertex. -/
def exitSlot (i : Fin (m + n)) : Fin 3 :=
  match step i with
  | .inl _ => 0
  | .inr _ => 1

theorem sweep_slots_distinct (i : Fin (m + n)) :
    entrySlot a j step i ≠ exitSlot a j step i ∧
    entrySlot a j step i ≠ 2 ∧ exitSlot a j step i ≠ 2 := by
  unfold entrySlot exitSlot
  cases step i <;> simp

/-- At each step the oriented entering edge is the reverse of the physical row pair. -/
theorem sweep_entryEdge (sorted : StrictMono (midpointKey ∘ step)) (i : Fin (m + n)) :
    orientedChordEdge (Tri i) (entrySlot a j step i) = (Sweep i.castSucc).swap := by
  unfold entrySlot latitudeSweepChordVertices
  rcases advance : step i with b | b
  · have h := (sweep_lower_coordinates a j step sorted i b advance).1
    exact Prod.ext rfl (congrArg Prod.fst h).symm
  · have h := (sweep_upper_coordinates a j step sorted i b advance).1
    exact Prod.ext (congrArg Prod.snd h).symm rfl

/-- At each step the oriented leaving edge is the physical row pair at the next time. -/
theorem sweep_exitEdge (sorted : StrictMono (midpointKey ∘ step)) (i : Fin (m + n)) :
    orientedChordEdge (Tri i) (exitSlot a j step i) = Sweep i.succ := by
  unfold exitSlot latitudeSweepChordVertices
  rcases advance : step i with b | b
  · have h := (sweep_lower_coordinates a j step sorted i b advance).2
    exact h.symm
  · have h := (sweep_upper_coordinates a j step sorted i b advance).2
    exact h.symm

/-- The final cross-row edge of each step is the initial edge of its
cyclic successor, as a literal pair of unit sites. -/
theorem latitudeSweepCrossSites_next (m_pos : 0 < m) (n_pos : 0 < n) (i : Fin (m + n)) :
    Sweep (finRotate (m + n) i).castSucc = Sweep i.succ := by
  have total : 1 < m + n := by omega
  let : NeZero (m + n) := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt total)⟩
  have next : (finRotate (m + n) i).val = (i.val + 1) % (m + n) := by
    simp [finRotate_apply, Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt total]
  by_cases before : i.val + 1 < m + n
  · have equal : (finRotate (m + n) i).castSucc = i.succ :=
      Fin.ext (by simpa only [Fin.val_castSucc, Fin.val_succ, next, Nat.mod_eq_of_lt before])
    rw [equal]
  · have at_last : i.val + 1 = m + n := by omega
    have after : i.succ = Fin.last (m + n) := Fin.ext at_last
    have at_start : (finRotate (m + n) i).castSucc = 0 :=
      Fin.ext (by simp only [Fin.val_castSucc, next, at_last, Nat.mod_self, Fin.val_zero])
    rw [after, at_start, latitudeSweepCrossSites_last a j step m_pos n_pos]

/-- The literal entering and leaving slots match at each successor, including wraparound. -/
theorem sweep_next_opposite_slots (sorted : StrictMono (midpointKey ∘ step))
    (m_pos : 0 < m) (n_pos : 0 < n) (i : Fin (m + n)) :
    orientedChordEdge (Tri (finRotate (m + n) i))
      (entrySlot a j step (finRotate (m + n) i)) =
        (orientedChordEdge (Tri i) (exitSlot a j step i)).swap := by
  rw [sweep_entryEdge a j step sorted, sweep_exitEdge a j step sorted,
    latitudeSweepCrossSites_next a j step m_pos n_pos]

/-- The two actual cyclic triangles traverse their shared cross-row edge in reverse orders. -/
theorem latitudeSweepChord_next_pairs (sorted : StrictMono (midpointKey ∘ step))
    (m_pos : 0 < m) (n_pos : 0 < n) (i : Fin (m + n)) :
    let edge := Sweep i.succ
    CyclicTriangleEdge (Tri i) edge.1 edge.2 ∧
      CyclicTriangleEdge (Tri (finRotate (m + n) i)) edge.2 edge.1 := by
  have first := (latitudeSweepChord_cross_edges a j step sorted i).2
  have last := (latitudeSweepChord_cross_edges a j step sorted (finRotate (m + n) i)).1
  change CyclicTriangleEdge (Tri _) (Sweep (finRotate (m + n) i).castSucc).2
    (Sweep (finRotate (m + n) i).castSucc).1 at last
  rw [latitudeSweepCrossSites_next a j step m_pos n_pos i] at last
  exact ⟨first, last⟩

/-- Each lower-row segment occurs as a forward base exactly at its lower advance. -/
theorem latitudeSweepChord_lower_base (e : Fin m) :
    CyclicTriangleEdge (Tri (lowerRank step e))
      (rowSite a j e.val) (rowSite a j (e.val + 1)) := by
  unfold latitudeSweepChordVertices lowerRank
  rw [step.apply_symm_apply]
  exact Or.inl ⟨rfl, rfl⟩

/-- Each upper-row segment occurs as a reverse base exactly at its upper advance. -/
theorem latitudeSweepChord_upper_base (e : Fin n) :
    CyclicTriangleEdge (Tri (upperRank step e))
      (rowSite a (j + 1) (e.val + 1)) (rowSite a (j + 1) e.val) := by
  unfold latitudeSweepChordVertices upperRank
  rw [step.apply_symm_apply]
  exact Or.inl ⟨rfl, rfl⟩

end Unfoldings.FewestNets.AcuteLatitudeGrid
