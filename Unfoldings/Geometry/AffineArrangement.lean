module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Baire.Lemmas

/-!
# Finite affine arrangements and regular closed sets

This layer is independent of unfolding geometry. A regular closed set whose
boundary lies in finitely many proper affine hyperplanes is a finite union of
closed chambers. Each nonempty chamber closure is given by the corresponding
finite family of weak affine inequalities.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]

def signed (f : E →ᵃ[ℝ] ℝ) (positive : Bool) : E →ᵃ[ℝ] ℝ :=
  if positive then f else -f

omit [FiniteDimensional ℝ E] in
@[simp] theorem signed_apply (f : E →ᵃ[ℝ] ℝ) (positive : Bool) (x : E) :
    signed f positive x = if positive then f x else -f x := by
  cases positive <;> rfl

def chamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) : Set E :=
  {x | ∀ i, 0 < signed (f i) (signs i) x}

def closedChamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) : Set E :=
  {x | ∀ i, 0 ≤ signed (f i) (signs i) x}

theorem isOpen_chamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) :
    IsOpen (chamber f signs) := by
  have equal : chamber f signs = ⋂ i, {x | 0 < signed (f i) (signs i) x} := by ext; simp [chamber]
  rw [equal]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
    (signed (f i) (signs i)).continuous_of_finiteDimensional)

omit [Finite ι] in
theorem isClosed_closedChamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) :
    IsClosed (closedChamber f signs) := by
  have equal : closedChamber f signs = ⋂ i, {x | 0 ≤ signed (f i) (signs i) x} := by
    ext; simp [closedChamber]
  rw [equal]
  exact isClosed_iInter (fun i => isClosed_le continuous_const
    (signed (f i) (signs i)).continuous_of_finiteDimensional)

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem convex_chamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) :
    Convex ℝ (chamber f signs) := by
  have equal : chamber f signs = ⋂ i, (signed (f i) (signs i)) ⁻¹' Set.Ioi 0 := by
    ext; simp [chamber]
  rw [equal]
  exact convex_iInter (fun i => (convex_Ioi (0 : ℝ)).affine_preimage _)

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem convex_closedChamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) :
    Convex ℝ (closedChamber f signs) := by
  have equal : closedChamber f signs = ⋂ i, (signed (f i) (signs i)) ⁻¹' Set.Ici 0 := by
    ext; simp [closedChamber]
  rw [equal]
  exact convex_iInter (fun i => (convex_Ici (0 : ℝ)).affine_preimage _)

omit [Finite ι] in
theorem closure_chamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool)
    (nonempty : (chamber f signs).Nonempty) :
    closure (chamber f signs) = closedChamber f signs := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx i => (hx i).le) (isClosed_closedChamber f signs)
  · obtain ⟨a, ha⟩ := nonempty
    intro x hx
    have segment : openSegment ℝ a x ⊆ chamber f signs := by
      intro y member i
      obtain ⟨t, ht, rfl⟩ := (openSegment_eq_image_lineMap ℝ a x).le member
      rw [(signed (f i) (signs i)).apply_lineMap, AffineMap.lineMap_apply_module]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht.2) (ha i)) (mul_nonneg ht.1.le (hx i))
    exact closure_mono segment (segment_subset_closure_openSegment (right_mem_segment ℝ a x))

omit [FiniteDimensional ℝ E] in
theorem dense_nonzero (f : E →ᵃ[ℝ] ℝ) (nonzero : f ≠ 0) :
    Dense {x | f x ≠ 0} := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x member
  apply nonzero
  exact AffineMap.ext_on (isOpen_interior.affineSpan_eq_top ⟨x, member⟩)
    (by
      intro y hy
      have zero : y ∈ {z : E | f z = 0} := interior_subset hy
      exact zero)

theorem dense_regular (f : ι → E →ᵃ[ℝ] ℝ) (nonzero : ∀ i, f i ≠ 0) :
    Dense {x | ∀ i, f i x ≠ 0} := by
  have dense := (Set.finite_range (fun i => {x | f i x ≠ 0})).dense_sInter
    (by rintro _ ⟨i, rfl⟩; exact
      (isClosed_eq (f i).continuous_of_finiteDimensional continuous_const).isOpen_compl)
    (by rintro _ ⟨i, rfl⟩; exact dense_nonzero (f i) (nonzero i))
  convert dense using 1
  ext x
  simp

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem exists_chamber_of_regular (f : ι → E →ᵃ[ℝ] ℝ) {x : E}
    (regular : ∀ i, f i x ≠ 0) : ∃ signs, x ∈ chamber f signs := by
  classical
  refine ⟨fun i => decide (0 < f i x), ?_⟩
  intro i
  by_cases positive : 0 < f i x
  · simp [positive]
  · have negative : f i x < 0 := lt_of_le_of_ne (le_of_not_gt positive) (regular i)
    simpa [positive] using neg_pos.mpr negative

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem chamber_avoids_zero (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool)
    {x : E} (member : x ∈ chamber f signs) (i : ι) : f i x ≠ 0 := by
  intro zero
  have positive := member i
  simp [zero] at positive

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem chamber_subset_interior (f : ι → E →ᵃ[ℝ] ℝ) {s : Set E}
    (support : ∀ x ∈ frontier s, ∃ i, f i x = 0) (signs : ι → Bool)
    (meets : (chamber f signs ∩ interior s).Nonempty) : chamber f signs ⊆ interior s := by
  apply (convex_chamber f signs).isPreconnected.subset_of_closure_inter_subset
    isOpen_interior meets
  intro x member
  by_contra outside
  have boundary : x ∈ frontier s := by
    rw [frontier]
    exact ⟨closure_mono interior_subset member.1, outside⟩
  obtain ⟨i, zero⟩ := support x boundary
  exact chamber_avoids_zero f signs member.2 i zero

theorem interior_closedChamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool)
    (nonempty : (chamber f signs).Nonempty) :
    interior (closedChamber f signs) = chamber f signs := by
  rw [← closure_chamber f signs nonempty]
  have inside : (interior (chamber f signs)).Nonempty := by
    rwa [(isOpen_chamber f signs).interior_eq]
  rw [(convex_chamber f signs).interior_closure_eq_interior_of_nonempty_interior inside,
    (isOpen_chamber f signs).interior_eq]

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem chamber_signs_unique (f : ι → E →ᵃ[ℝ] ℝ) {a b : ι → Bool} {x : E}
    (ha : x ∈ chamber f a) (hb : x ∈ chamber f b) : a = b := by
  funext i
  have positive_a := ha i
  have positive_b := hb i
  cases h_a : a i <;> cases h_b : b i <;> try rfl
  all_goals
    simp only [signed_apply, h_a, h_b, Bool.false_eq_true, ↓reduceIte]
      at positive_a positive_b
    linarith

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem chamber_positive_of_nonnegative (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool)
    {x y : E} (hx : x ∈ chamber f signs) (hy : y ∈ chamber f signs) (i : ι)
    (nonnegative : 0 ≤ f i x) : 0 < f i y := by
  have positive_x := hx i
  have positive_y := hy i
  cases h : signs i
  · have negative : 0 < -f i x := by simpa [h] using positive_x
    linarith
  · simpa [h] using positive_y

theorem exists_finite_closed_chamber_cover (f : ι → E →ᵃ[ℝ] ℝ)
    (nonzero : ∀ i, f i ≠ 0) {s : Set E} (compact : IsCompact s)
    (regular_closed : closure (interior s) = s)
    (support : ∀ x ∈ frontier s, ∃ i, f i x = 0) :
    ∃ S : Set (ι → Bool), S.Finite ∧
      (∀ signs ∈ S, (chamber f signs).Nonempty ∧
        chamber f signs ⊆ interior s ∧ IsCompact (closedChamber f signs)) ∧
      s = ⋃ signs ∈ S, closedChamber f signs := by
  let S := {signs | (chamber f signs ∩ interior s).Nonempty}
  have finite : S.Finite := Set.toFinite _
  have contained (signs : ι → Bool) (member : signs ∈ S) : chamber f signs ⊆ interior s :=
    chamber_subset_interior f support signs member
  have nonempty (signs : ι → Bool) (member : signs ∈ S) : (chamber f signs).Nonempty :=
    member.mono (fun _ hx => hx.1)
  have closed_contained (signs : ι → Bool) (member : signs ∈ S) : closedChamber f signs ⊆ s := by
    rw [← closure_chamber f signs (nonempty signs member)]
    exact closure_minimal ((contained signs member).trans interior_subset) compact.isClosed
  let cover := ⋃ signs ∈ S, closedChamber f signs
  have closed_cover : IsClosed cover :=
    finite.isClosed_biUnion (fun signs _ => isClosed_closedChamber f signs)
  have regular_covered : interior s ∩ {x | ∀ i, f i x ≠ 0} ⊆ cover := by
    intro x hx
    obtain ⟨signs, member⟩ := exists_chamber_of_regular f hx.2
    exact Set.mem_iUnion.mpr ⟨signs, Set.mem_iUnion.mpr
      ⟨⟨x, member, hx.1⟩, fun i => (member i).le⟩⟩
  have interior_covered : interior s ⊆ cover :=
    ((dense_regular f nonzero).open_subset_closure_inter isOpen_interior).trans
      (closure_minimal regular_covered closed_cover)
  refine ⟨S, finite, ?_, Set.Subset.antisymm ?_ ?_⟩
  · intro signs member
    exact ⟨nonempty signs member, contained signs member,
      compact.of_isClosed_subset (isClosed_closedChamber f signs) (closed_contained signs member)⟩
  · rw [← regular_closed]
    exact closure_minimal interior_covered closed_cover
  · intro x hx
    obtain ⟨signs, member, point⟩ := Set.mem_iUnion₂.mp hx
    exact closed_contained signs member point

end Unfoldings.AffineArrangement
