module

public import Unfoldings.FewestNets.CheckedMeshPerimeter
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.TakeDrop
public import Batteries.Data.List.Lemmas

/-! Reconstruction and summation of consecutive blocks of finite keys. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

private theorem flatten_keyBlocks_append_drop {ι : Type*} (keys : List ι) (size n : ℕ) :
    (List.ofFn (fun i : Fin n => (keys.drop (size * i.val)).take size)).flatten ++
      keys.drop (size * n) = keys := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.append_assoc, Nat.mul_succ, List.drop_take_append_drop, ih]

theorem flatten_keyBlocks_eq_of_length_le {ι : Type*} (keys : List ι) (size n : ℕ)
    (covers : keys.length ≤ size * n) :
    (List.ofFn (fun i : Fin n => (keys.drop (size * i.val)).take size)).flatten = keys := by
  have h := flatten_keyBlocks_append_drop keys size n
  simpa only [List.drop_eq_nil_of_le covers, List.append_nil] using h

theorem sum_map_eq_sum_keyBlocks {ι : Type*} (keys : List ι) (size n : ℕ)
    (covers : keys.length ≤ size * n) (f : ι → ℝ) :
    (keys.map f).sum = ∑ i : Fin n, (((keys.drop (size * i.val)).take size).map f).sum := by
  have cover := flatten_keyBlocks_eq_of_length_le keys size n covers
  nth_rw 1 [← cover]
  rw [List.map_flatten, List.sum_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]

end Unfoldings.FewestNets
