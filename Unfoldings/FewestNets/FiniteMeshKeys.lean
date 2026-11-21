module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.List.Range
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! The exact combinatorial keys of the finite normal-mesh certificates. -/

@[expose] public section

namespace Unfoldings.FewestNets

open scoped BigOperators

/-- The face-interior key uses the two smaller positive barycentric weights. -/
def faceMeshKeys (q : ℕ) : List (ℕ × ℕ) :=
  (List.range q).flatMap fun i =>
    (List.range' 1 (min i (q - 2 * i))).map (Prod.mk i)

/-- A macroedge key records the larger of its two positive barycentric weights. -/
def seamMeshKeys (q : ℕ) : List ℕ :=
  List.range' ((q + 1) / 2) (q - (q + 1) / 2)

theorem mem_faceMeshKeys {q i j : ℕ} :
    (i, j) ∈ faceMeshKeys q ↔ 1 ≤ j ∧ j ≤ i ∧ 2 * i + j ≤ q := by
  simp only [faceMeshKeys, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'_1,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, l, ⟨hl, hl'⟩, rfl, rfl⟩
    exact ⟨hl, by omega, by omega⟩
  · rintro ⟨pos, order, bound⟩
    exact ⟨i, by omega, j, ⟨pos, by omega⟩, rfl, rfl⟩

theorem mem_seamMeshKeys {q i : ℕ} :
    i ∈ seamMeshKeys q ↔ (q + 1) / 2 ≤ i ∧ i < q := by
  simp only [seamMeshKeys, List.mem_range'_1]
  omega

/-- Every positive barycentric triple is represented by one canonical face key. -/
theorem exists_faceMeshKey_of_weights {q : ℕ} (weight : Fin 3 → ℕ)
    (positive : ∀ j, 0 < weight j) (total : (∑ j, weight j) = q) :
    ∃ (i j : ℕ) (σ : Equiv.Perm (Fin 3)), (i, j) ∈ faceMeshKeys q ∧
      weight ∘ σ = ![j, i, q - i - j] := by
  let σ := Tuple.sort weight
  let j := weight (σ 0)
  let i := weight (σ 1)
  let k := weight (σ 2)
  have sorted := Tuple.monotone_sort weight
  have ji : j ≤ i := sorted (by decide : (0 : Fin 3) ≤ 1)
  have ik : i ≤ k := sorted (by decide : (1 : Fin 3) ≤ 2)
  have sum : j + i + k = q := by
    have h := (Equiv.sum_comp σ weight).trans total
    rwa [Fin.sum_univ_three] at h
  have j_pos : 0 < j := positive _
  refine ⟨i, j, σ, mem_faceMeshKeys.mpr ⟨j_pos, ji, by omega⟩, ?_⟩
  funext f
  fin_cases f
  · rfl
  · rfl
  · change k = q - i - j
    omega

/-- A permutation orbit cannot have two different canonical face keys. -/
theorem faceMeshKey_unique_of_permutation {q i j k l : ℕ}
    (first : (i, j) ∈ faceMeshKeys q) (last : (k, l) ∈ faceMeshKeys q)
    (σ : Equiv.Perm (Fin 3))
    (same : (![j, i, q - i - j] : Fin 3 → ℕ) ∘ σ = ![l, k, q - k - l]) :
    (i, j) = (k, l) := by
  have ordered {a b : ℕ} (h : (a, b) ∈ faceMeshKeys q) :
      Monotone (![b, a, q - a - b] : Fin 3 → ℕ) := by
    have bound := mem_faceMeshKeys.mp h
    intro x y xy
    fin_cases x <;> fin_cases y <;> simp_all <;> omega
  let f : Fin 3 → ℕ := ![j, i, q - i - j]
  have monotone_also : Monotone (f ∘ σ) := same.symm ▸ ordered last
  have h : f ∘ σ = f ∘ Tuple.sort f :=
    Tuple.comp_sort_eq_comp_iff_monotone.mpr monotone_also
  have identity : Tuple.sort f = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr (ordered first)
  rw [identity] at h
  have same_tuple : (![j, i, q - i - j] : Fin 3 → ℕ) = ![l, k, q - k - l] :=
    h.symm.trans same
  exact Prod.ext (congrFun same_tuple 1) (congrFun same_tuple 0)

/-- The two positive weights of an interior macroedge site give a canonical seam key. -/
theorem max_mem_seamMeshKeys {q a b : ℕ} (a_pos : 0 < a) (b_pos : 0 < b)
    (sum : a + b = q) : max a b ∈ seamMeshKeys q := by
  apply mem_seamMeshKeys.mpr
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

theorem length_faceMeshKeys (q : ℕ) :
    (faceMeshKeys q).length =
      ((List.range q).map (fun i => min i (q - 2 * i))).sum := by
  simp only [faceMeshKeys, List.length_flatMap, List.length_map, List.length_range']

set_option maxRecDepth 4096 in
-- The kernel reduces the sum of four hundred row lengths.
theorem normalMeshKeys_q100_q400 :
    (faceMeshKeys 100).length = 833 ∧ (seamMeshKeys 100).length = 50 ∧
    (faceMeshKeys 400).length = 13333 ∧ (seamMeshKeys 400).length = 200 := by
  rw [length_faceMeshKeys, length_faceMeshKeys]
  decide

/-- All orderings of the three barycentric weights in a face key. -/
noncomputable def faceWeightOrbit (weight : Fin 3 → ℕ) : Finset (Fin 3 → ℕ) :=
  Finset.univ.image fun σ : Equiv.Perm (Fin 3) => weight ∘ σ

private theorem faceWeightOrbit_card_of_constant {weight : Fin 3 → ℕ} {c : ℕ}
    (constant : ∀ i, weight i = c) : (faceWeightOrbit weight).card = 1 := by
  classical
  have orbit : faceWeightOrbit weight = {weight} := by
    ext f
    constructor
    · intro hf
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hf
      apply Finset.mem_singleton.mpr
      funext i
      exact (constant _).trans (constant i).symm
    · intro hf
      obtain rfl := Finset.mem_singleton.mp hf
      exact Finset.mem_image.mpr ⟨Equiv.refl _, Finset.mem_univ _, rfl⟩
  rw [orbit, Finset.card_singleton]

private theorem faceWeightOrbit_card_of_injective {weight : Fin 3 → ℕ}
    (injective : Function.Injective weight) : (faceWeightOrbit weight).card = 6 := by
  classical
  have perm_injective : Function.Injective (fun σ : Equiv.Perm (Fin 3) => weight ∘ σ) := by
    intro σ τ h
    apply Equiv.ext
    intro i
    exact injective (congrFun h i)
  rw [faceWeightOrbit, Finset.card_image_of_injective _ perm_injective,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  decide

private theorem faceWeightOrbit_card_of_two_equal (weight : Fin 3 → ℕ) (k : Fin 3) (c : ℕ)
    (odd : weight k ≠ c) (other : ∀ j, j ≠ k → weight j = c) :
    (faceWeightOrbit weight).card = 3 := by
  classical
  let withOdd (j : Fin 3) (i : Fin 3) := if i = j then weight k else c
  have injective : Function.Injective withOdd := by
    intro a b h
    by_contra distinct
    have value := congrFun h a
    exact odd (by simpa only [withOdd, ite_eq_left rfl, ite_eq_right distinct] using value)
  have locate (σ : Equiv.Perm (Fin 3)) : weight ∘ σ = withOdd (σ.symm k) := by
    funext j
    by_cases location : j = σ.symm k
    · rw [location]
      simp only [Function.comp_apply, Equiv.apply_symm_apply, withOdd, ite_eq_left rfl]
    · have neq : σ j ≠ k := fun h => location (σ.eq_symm_apply.mpr h)
      change weight (σ j) = (if j = σ.symm k then weight k else c)
      rw [ite_eq_right location]
      exact other _ neq
  have orbit : faceWeightOrbit weight = Finset.univ.image withOdd := by
    ext f
    constructor
    · intro hf
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_image.mpr ⟨σ.symm k, Finset.mem_univ _, (locate σ).symm⟩
    · intro hf
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
      let σ := Equiv.swap k j
      have where_odd : σ.symm k = j := by
        apply σ.injective
        rw [σ.apply_symm_apply]
        exact (Equiv.swap_apply_right k j).symm
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, (locate σ).trans (by rw [where_odd])⟩
  rw [orbit, Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_fin]

/-- The symmetry weight of a face key equals its number of distinct orderings. -/
def faceMeshKeyWeight (q i j : ℕ) : ℕ :=
  if j = i then (if i = q - i - j then 1 else 3)
  else if i = q - i - j then 3 else 6

theorem faceWeightOrbit_card_eq_meshKeyWeight {q i j : ℕ}
    (key : (i, j) ∈ faceMeshKeys q) :
    (faceWeightOrbit (![j, i, q - i - j] : Fin 3 → ℕ)).card = faceMeshKeyWeight q i j := by
  let k := q - i - j
  let weight : Fin 3 → ℕ := ![j, i, k]
  have bounds := mem_faceMeshKeys.mp key
  have i_le : i ≤ k := by dsimp [k]; omega
  change (faceWeightOrbit weight).card = if j = i then (if i = k then 1 else 3)
    else if i = k then 3 else 6
  by_cases ji : j = i
  · by_cases ik : i = k
    · simp only [ite_eq_left ji, ite_eq_left ik]
      apply faceWeightOrbit_card_of_constant (c := k)
      intro f
      fin_cases f <;> simp [weight, ji, ik]
    · simp only [ite_eq_left ji, ite_eq_right ik]
      apply faceWeightOrbit_card_of_two_equal weight 2 i
      · exact Ne.symm ik
      · intro f h
        fin_cases f <;> simp_all [weight]
  · by_cases ik : i = k
    · simp only [ite_eq_right ji, ite_eq_left ik]
      apply faceWeightOrbit_card_of_two_equal weight 0 i
      · exact ji
      · intro f h
        fin_cases f <;> simp_all [weight]
    · simp only [ite_eq_right ji, ite_eq_right ik]
      apply faceWeightOrbit_card_of_injective
      apply StrictMono.injective
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all [weight] <;> omega

/-- All orderings of the two barycentric weights in a seam key. -/
def seamWeightOrbit (q i : ℕ) : Finset (ℕ × ℕ) :=
  {(i, q - i), (q - i, i)}

/-- The symmetry weight of a seam key equals its number of distinct orderings. -/
def seamMeshKeyWeight (q i : ℕ) : ℕ := if 2 * i = q then 1 else 2

theorem seamWeightOrbit_card_eq_meshKeyWeight {q i : ℕ} (key : i ∈ seamMeshKeys q) :
    (seamWeightOrbit q i).card = seamMeshKeyWeight q i := by
  have bounds := mem_seamMeshKeys.mp key
  by_cases midpoint : 2 * i = q
  · have eq : q - i = i := by omega
    simp [seamWeightOrbit, seamMeshKeyWeight, midpoint, eq]
  · have distinct : (i, q - i) ≠ (q - i, i) := fun h => by
      have eq : i = q - i := congrArg Prod.fst h
      omega
    rw [seamMeshKeyWeight, ite_eq_right midpoint, seamWeightOrbit, Finset.card_pair distinct]

private theorem sum_faceMeshKeyWeight_row (q i : ℕ) :
    ((List.range' 1 (min i (q - 2 * i))).map (faceMeshKeyWeight q i)).sum =
      let m := min i (q - 2 * i)
      if m = 0 then 0 else 6 * (m - 1) + if 3 * i = q then 1 else 3 := by
  let m := min i (q - 2 * i)
  change ((List.range' 1 m).map (faceMeshKeyWeight q i)).sum =
    if m = 0 then 0 else 6 * (m - 1) + if 3 * i = q then 1 else 3
  cases hm : m with
  | zero => simp
  | succ n =>
    have range_last : 1 + n = m := by omega
    have m_le : m ≤ i := min_le_left _ _
    have m_bound : 2 * i + m ≤ q := by
      have bound : m ≤ q - 2 * i := min_le_right _ _
      omega
    have weight_prefix : (List.range' 1 n).map (faceMeshKeyWeight q i) =
        (List.range' 1 n).map (fun _ => 6) := by
      apply List.map_congr_left
      intro j hj
      have j_bound := List.mem_range'_1.mp hj
      have ji : j ≠ i := by omega
      have ik : i ≠ q - i - j := by omega
      simp [faceMeshKeyWeight, ji, ik]
    have weight_last : faceMeshKeyWeight q i m = if 3 * i = q then 1 else 3 := by
      by_cases mi : m = i
      · have eq_iff : i = q - i - m ↔ 3 * i = q := by omega
        simp only [faceMeshKeyWeight, ite_eq_left mi, eq_iff]
      · have min_right : m = q - 2 * i := by
          by_cases le : i ≤ q - 2 * i
          · exact False.elim (mi (min_eq_left le))
          · exact min_eq_right (by omega)
        have ik : i = q - i - m := by omega
        have not_thirds : 3 * i ≠ q := by omega
        simp only [faceMeshKeyWeight, ite_eq_right mi, ite_eq_left ik, ite_eq_right not_thirds]
    rw [List.range'_1_concat, List.map_append, List.sum_append_nat, weight_prefix,
      List.map_const', List.length_range', List.sum_replicate_nat, range_last]
    change n * 6 + (faceMeshKeyWeight q i m + 0) =
      if n + 1 = 0 then 0 else 6 * (n + 1 - 1) + if 3 * i = q then 1 else 3
    rw [weight_last, ite_eq_right (Nat.succ_ne_zero n)]
    omega

theorem sum_faceMeshKeyWeights (q : ℕ) :
    ((faceMeshKeys q).map (fun key => faceMeshKeyWeight q key.1 key.2)).sum =
      ((List.range q).map (fun i =>
        let m := min i (q - 2 * i)
        if m = 0 then 0 else 6 * (m - 1) + if 3 * i = q then 1 else 3)).sum := by
  simp only [faceMeshKeys, List.map_flatMap, List.map_map, Function.comp_def]
  generalize List.range q = rows
  induction rows with
  | nil => rfl
  | cons i rows ih =>
    simp only [List.flatMap_cons, List.sum_append_nat, List.map_cons, List.sum_cons,
      sum_faceMeshKeyWeight_row, ih]

set_option maxRecDepth 4096 in
/-- The orbit-weighted counts within one macroface and one macroedge. -/
theorem normalMeshKeyWeights_q100_q400 :
    ((faceMeshKeys 100).map (fun key => faceMeshKeyWeight 100 key.1 key.2)).sum = 4851 ∧
    ((seamMeshKeys 100).map (seamMeshKeyWeight 100)).sum = 99 ∧
    ((faceMeshKeys 400).map (fun key => faceMeshKeyWeight 400 key.1 key.2)).sum = 79401 ∧
    ((seamMeshKeys 400).map (seamMeshKeyWeight 400)).sum = 399 := by
  rw [sum_faceMeshKeyWeights, sum_faceMeshKeyWeights]
  decide

end Unfoldings.FewestNets
