module

public import Unfoldings.FewestNets.AcuteLatitudeRows
public import Unfoldings.FewestNets.LatitudeFiniteSites

/-! The actual annular sweep keeps the same cross-row edges across successive steps and the seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- The actual colatitude and periodic longitude of a numbered sample. -/
def rowSite (a : ℝ) (j k : ℕ) : Space :=
  latitudeSite (colatitude a j) (rowLongitude (rowSize a j) k)

theorem rowSite_mod (a : ℝ) (j k : ℕ) (positive : 0 < rowSize a j) :
    rowSite a j (k % rowSize a j) = rowSite a j k := by
  let n := rowSize a j
  have n_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr positive.ne'
  have sum : (k : ℝ) = (k % n : ℕ) + (n : ℝ) * (k / n : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k n).symm
  have units : rowLongitude n k = rowLongitude n (k % n) + ((k / n : ℕ) : ℝ) * (2 * π) := by
    unfold rowLongitude
    rw [sum]
    field_simp [n_pos]
  change latitudeSite (colatitude a j) (rowLongitude n (k % n)) =
    latitudeSite (colatitude a j) (rowLongitude n k)
  rw [units, ← Int.cast_natCast]
  exact (latitudeSite_add_int_mul_two_pi _ _ _).symm

/-- A deterministic order of advances on the lower and upper rows. -/
def sweepOrder (m n : ℕ) : Fin (m + n) ≃ Fin m ⊕ Fin n :=
  Classical.choose (exists_midpointOrder (lower := m) (upper := n))

theorem sweepOrder_sorted (m n : ℕ) : StrictMono (midpointKey ∘ sweepOrder m n) :=
  Classical.choose_spec (exists_midpointOrder (lower := m) (upper := n))

/-- The annular triangles are indexed by strip and advance. -/
abbrev AnnularTriangle (a : ℝ) :=
  Σ j : Fin (stripCount a), Fin (rowSize a j.val + rowSize a (j.val + 1))

theorem card_annularTriangle (a : ℝ) :
    Fintype.card (AnnularTriangle a) = triangleCount a := by
  rw [Fintype.card_sigma, triangleCount, ← Fin.sum_univ_eq_sum_range]
  simp only [Fintype.card_fin]

variable (a : ℝ) (j : ℕ)

local notation "m" => rowSize a j
local notation "n" => rowSize a (j + 1)
variable (step : Fin (rowSize a j + rowSize a (j + 1)) ≃
  Fin (rowSize a j) ⊕ Fin (rowSize a (j + 1)))

/-- The actual pair of sampled sites at a sweep time. -/
def latitudeSweepCrossSites (time : Fin (m + n + 1)) : Space × Space :=
  (rowSite a j (rowProgress (lowerRank step) time.val),
    rowSite a (j + 1) (rowProgress (upperRank step) time.val))

/-- The lower base is oriented by increasing longitude and the upper base by decreasing longitude. -/
def latitudeSweepChordVertices (i : Fin (m + n)) : Fin 3 → Space :=
  match step i with
  | .inl b => ![rowSite a j b.val, rowSite a j (b.val + 1),
      (latitudeSweepCrossSites a j step i.castSucc).2]
  | .inr b => ![rowSite a (j + 1) (b.val + 1), rowSite a (j + 1) b.val,
      (latitudeSweepCrossSites a j step i.castSucc).1]

theorem range_finThree_sites (x y z : Space) : Set.range ![x, y, z] = ({x, y, z} : Set Space) := by
  ext q
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp
  · intro member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- An actual triangle has this oriented edge in its cyclic vertex order. -/
def CyclicTriangleEdge (vertices : Fin 3 → Space) (x y : Space) : Prop :=
  (vertices 0 = x ∧ vertices 1 = y) ∨
    (vertices 1 = x ∧ vertices 2 = y) ∨ (vertices 2 = x ∧ vertices 0 = y)

theorem sweep_lower_coordinates (sorted : StrictMono (midpointKey ∘ step))
    (i : Fin (m + n)) (b : Fin m) (which : step i = .inl b) :
    latitudeSweepCrossSites a j step i.castSucc =
      (rowSite a j b.val, (latitudeSweepCrossSites a j step i.castSucc).2) ∧
    latitudeSweepCrossSites a j step i.succ =
      (rowSite a j (b.val + 1), (latitudeSweepCrossSites a j step i.castSucc).2) := by
  have at_rank : lowerRank step b = i := by
    rw [lowerRank, ← which, step.symm_apply_apply]
  have lower := rowProgress_at_rank _ (lowerRank_strictMono step sorted) b
  have after := rowProgress_succ_eq_of_edge _ (lowerRank_strictMono step sorted).injective b
  rw [at_rank] at lower after
  have upper : rowProgress (upperRank step) (i.val + 1) = rowProgress (upperRank step) i.val := by
    apply rowProgress_succ_eq_of_no_edge
    intro k equal
    have same := congrArg step (Fin.ext equal : upperRank step k = i)
    rw [upperRank, step.apply_symm_apply, which] at same
    cases same
  simp only [latitudeSweepCrossSites, Fin.val_castSucc, Fin.val_succ, lower, after, upper, and_self]

theorem sweep_upper_coordinates (sorted : StrictMono (midpointKey ∘ step))
    (i : Fin (m + n)) (b : Fin n) (which : step i = .inr b) :
    latitudeSweepCrossSites a j step i.castSucc =
      ((latitudeSweepCrossSites a j step i.castSucc).1, rowSite a (j + 1) b.val) ∧
    latitudeSweepCrossSites a j step i.succ =
      ((latitudeSweepCrossSites a j step i.castSucc).1, rowSite a (j + 1) (b.val + 1)) := by
  have at_rank : upperRank step b = i := by
    rw [upperRank, ← which, step.symm_apply_apply]
  have upper := rowProgress_at_rank _ (upperRank_strictMono step sorted) b
  have after := rowProgress_succ_eq_of_edge _ (upperRank_strictMono step sorted).injective b
  rw [at_rank] at upper after
  have lower : rowProgress (lowerRank step) (i.val + 1) = rowProgress (lowerRank step) i.val := by
    apply rowProgress_succ_eq_of_no_edge
    intro k equal
    have same := congrArg step (Fin.ext equal : lowerRank step k = i)
    rw [lowerRank, step.apply_symm_apply, which] at same
    cases same
  simp only [latitudeSweepCrossSites, Fin.val_castSucc, Fin.val_succ, upper, after, lower, and_self]

/-- Each triangle enters at the reversed initial cross edge and leaves at the forward final cross edge. -/
theorem latitudeSweepChord_cross_edges (sorted : StrictMono (midpointKey ∘ step)) (i : Fin (m + n)) :
    let first := latitudeSweepCrossSites a j step i.castSucc
    let last := latitudeSweepCrossSites a j step i.succ
    CyclicTriangleEdge (latitudeSweepChordVertices a j step i) first.2 first.1 ∧
      CyclicTriangleEdge (latitudeSweepChordVertices a j step i) last.1 last.2 := by
  dsimp only
  unfold latitudeSweepChordVertices CyclicTriangleEdge
  rcases which : step i with b | b
  · obtain ⟨initial, final⟩ := sweep_lower_coordinates a j step sorted i b which
    exact ⟨Or.inr (Or.inr ⟨rfl, (congrArg Prod.fst initial).symm⟩),
      Or.inr (Or.inl ⟨(congrArg Prod.fst final).symm, (congrArg Prod.snd final).symm⟩)⟩
  · obtain ⟨initial, final⟩ := sweep_upper_coordinates a j step sorted i b which
    exact ⟨Or.inr (Or.inl ⟨(congrArg Prod.snd initial).symm, rfl⟩),
      Or.inr (Or.inr ⟨(congrArg Prod.fst final).symm, (congrArg Prod.snd final).symm⟩)⟩

/-- The closing meridian uses the very same pair of unit sites as the opening meridian. -/
theorem latitudeSweepCrossSites_last (lower_pos : 0 < m) (upper_pos : 0 < n) :
    latitudeSweepCrossSites a j step (Fin.last (m + n)) = latitudeSweepCrossSites a j step 0 := by
  simp only [latitudeSweepCrossSites, Fin.val_last, Fin.val_zero, rowProgress_zero, rowProgress_end]
  congr 1
  · simpa only [Nat.mod_self] using (rowSite_mod a j m lower_pos).symm
  · simpa only [Nat.mod_self] using (rowSite_mod a (j + 1) n upper_pos).symm

/-- The actual three sampled sites in cyclic order after the midpoint advance. -/
def annularVertices (i : AnnularTriangle a) : Fin 3 → Space :=
  latitudeSweepChordVertices a i.1.val (sweepOrder _ _) i.2

theorem annularVertices_unit (i : AnnularTriangle a) (j : Fin 3) :
    ‖annularVertices a i j‖ = 1 := by
  unfold annularVertices latitudeSweepChordVertices
  cases sweepOrder _ _ i.2 <;> fin_cases j <;> exact latitudeSite_unit _ _

end Unfoldings.FewestNets.AcuteLatitudeGrid
