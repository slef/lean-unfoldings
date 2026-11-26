module

public import Unfoldings.FewestNets.LatitudeRings

/-! The actual annular sweep keeps the same cross-row edges across successive steps and the seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real

/-- The actual colatitude and periodic longitude of a numbered sample. -/
def rowSite (G : LatitudeRings) (j k : ℕ) : Space :=
  latitudeSite (colatitude G j) (rowLongitude (rowSize G j) k)

theorem rowSite_mod (G : LatitudeRings) (j k : ℕ) (positive : 0 < rowSize G j) :
    rowSite G j (k % rowSize G j) = rowSite G j k := by
  let n := rowSize G j
  have n_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr positive.ne'
  have sum : (k : ℝ) = (k % n : ℕ) + (n : ℝ) * (k / n : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k n).symm
  have units : rowLongitude n k = rowLongitude n (k % n) + ((k / n : ℕ) : ℝ) * (2 * π) := by
    unfold rowLongitude
    rw [sum]
    field_simp [n_pos]
  change latitudeSite (colatitude G j) (rowLongitude n (k % n)) =
    latitudeSite (colatitude G j) (rowLongitude n k)
  rw [units, ← Int.cast_natCast]
  exact (latitudeSite_add_int_mul_two_pi _ _ _).symm

/-- A deterministic order of advances on the lower and upper rows. -/
def sweepOrder (m n : ℕ) : Fin (m + n) ≃ Fin m ⊕ Fin n :=
  Classical.choose (exists_midpointOrder (lower := m) (upper := n))

theorem sweepOrder_sorted (m n : ℕ) : StrictMono (midpointKey ∘ sweepOrder m n) :=
  Classical.choose_spec (exists_midpointOrder (lower := m) (upper := n))

/-- The annular triangles are indexed by strip and advance. -/
abbrev AnnularTriangle (G : LatitudeRings) :=
  Σ j : Fin (stripCount G), Fin (rowSize G j.val + rowSize G (j.val + 1))

theorem card_annularTriangle (G : LatitudeRings) :
    Fintype.card (AnnularTriangle G) = triangleCount G := by
  rw [Fintype.card_sigma, triangleCount, ← Fin.sum_univ_eq_sum_range]
  simp only [Fintype.card_fin]

variable (G : LatitudeRings) (j : ℕ)

local notation "m" => rowSize G j
local notation "n" => rowSize G (j + 1)
variable (step : Fin (rowSize G j + rowSize G (j + 1)) ≃
  Fin (rowSize G j) ⊕ Fin (rowSize G (j + 1)))

/-- The actual pair of sampled sites at a sweep time. -/
def latitudeSweepCrossSites (time : Fin (m + n + 1)) : Space × Space :=
  (rowSite G j (rowProgress (lowerRank step) time.val),
    rowSite G (j + 1) (rowProgress (upperRank step) time.val))

/-- The lower base is oriented by increasing longitude and the upper base by decreasing longitude. -/
def latitudeSweepChordVertices (i : Fin (m + n)) : Fin 3 → Space :=
  match step i with
  | .inl b => ![rowSite G j b.val, rowSite G j (b.val + 1),
      (latitudeSweepCrossSites G j step i.castSucc).2]
  | .inr b => ![rowSite G (j + 1) (b.val + 1), rowSite G (j + 1) b.val,
      (latitudeSweepCrossSites G j step i.castSucc).1]

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
    latitudeSweepCrossSites G j step i.castSucc =
      (rowSite G j b.val, (latitudeSweepCrossSites G j step i.castSucc).2) ∧
    latitudeSweepCrossSites G j step i.succ =
      (rowSite G j (b.val + 1), (latitudeSweepCrossSites G j step i.castSucc).2) := by
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
    latitudeSweepCrossSites G j step i.castSucc =
      ((latitudeSweepCrossSites G j step i.castSucc).1, rowSite G (j + 1) b.val) ∧
    latitudeSweepCrossSites G j step i.succ =
      ((latitudeSweepCrossSites G j step i.castSucc).1, rowSite G (j + 1) (b.val + 1)) := by
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
    let first := latitudeSweepCrossSites G j step i.castSucc
    let last := latitudeSweepCrossSites G j step i.succ
    CyclicTriangleEdge (latitudeSweepChordVertices G j step i) first.2 first.1 ∧
      CyclicTriangleEdge (latitudeSweepChordVertices G j step i) last.1 last.2 := by
  dsimp only
  unfold latitudeSweepChordVertices CyclicTriangleEdge
  rcases which : step i with b | b
  · obtain ⟨initial, final⟩ := sweep_lower_coordinates G j step sorted i b which
    exact ⟨Or.inr (Or.inr ⟨rfl, (congrArg Prod.fst initial).symm⟩),
      Or.inr (Or.inl ⟨(congrArg Prod.fst final).symm, (congrArg Prod.snd final).symm⟩)⟩
  · obtain ⟨initial, final⟩ := sweep_upper_coordinates G j step sorted i b which
    exact ⟨Or.inr (Or.inl ⟨(congrArg Prod.snd initial).symm, rfl⟩),
      Or.inr (Or.inr ⟨(congrArg Prod.fst final).symm, (congrArg Prod.snd final).symm⟩)⟩

/-- The closing meridian uses the very same pair of unit sites as the opening meridian. -/
theorem latitudeSweepCrossSites_last (lower_pos : 0 < m) (upper_pos : 0 < n) :
    latitudeSweepCrossSites G j step (Fin.last (m + n)) = latitudeSweepCrossSites G j step 0 := by
  simp only [latitudeSweepCrossSites, Fin.val_last, Fin.val_zero, rowProgress_zero, rowProgress_end]
  congr 1
  · simpa only [Nat.mod_self] using (rowSite_mod G j m lower_pos).symm
  · simpa only [Nat.mod_self] using (rowSite_mod G (j + 1) n upper_pos).symm

/-- The actual three sampled sites in cyclic order after the midpoint advance. -/
def annularVertices (i : AnnularTriangle G) : Fin 3 → Space :=
  latitudeSweepChordVertices G i.1.val (sweepOrder _ _) i.2

theorem annularVertices_unit (i : AnnularTriangle G) (j : Fin 3) :
    ‖annularVertices G i j‖ = 1 := by
  unfold annularVertices latitudeSweepChordVertices
  cases sweepOrder _ _ i.2 <;> fin_cases j <;> exact latitudeSite_unit _ _

end Unfoldings.FewestNets.LatitudeRings
