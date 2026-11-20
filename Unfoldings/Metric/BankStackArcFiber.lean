module

public import Unfoldings.Metric.BankStackLocalClasses
public import Unfoldings.Topology.FiniteArcConcat
public import Mathlib.Data.List.Nodup

/-! The exact fiber at a physical point that meets a single original bank stack. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {G Edge : Type*} {Parameter : Edge → Type*}
  (X : Option G → Type*) [∀ i, EMetricSpace (X i)] (stack : Edge → List G)
  (base : ∀ e, Bool → Parameter e → X none)
  (gap : ∀ e g, g ∈ stack e → Bool → Parameter e → X (some g))

local notation "L" => bankStackLeft X stack base gap
local notation "R" => bankStackRight X stack base gap
local notation "Banks" => bankSeams L R
local notation "Point" => point X Banks

variable (e : Edge) (t : Parameter e)

local notation "N" => List.length (stack e)
local notation "Event[" i "]" => List.get (stack e) i
local notation "Member[" i "]" => List.get_mem (stack e) i
local notation "GapAt[" i "," flag "]" => gap e Event[i] Member[i] flag t

/-- The two tags at any consecutive seam of a nonempty stack are different. -/
private theorem stackTags_at_left (nodup : (stack e).Nodup)
    (k : Fin (N + 1)) (i : Fin N) (same : (L ⟨e, k⟩ t).1 = some Event[i]) : k = i.succ := by
  unfold bankStackLeft at same
  split at same
  · cases same
  · rename_i positive
    change k.val ≠ 0 at positive
    have bound : k.val < N + 1 := k.isLt
    have index : k.val - 1 < N := by omega
    have hit : (stack e)[k.val - 1]'index = (stack e)[i.val] := Option.some.inj same
    have eq := nodup.getElem_inj_iff.mp hit
    exact Fin.ext (by change k.val = i.val + 1; omega)

private theorem stackTags_at_right (nodup : (stack e).Nodup)
    (k : Fin (N + 1)) (i : Fin N) (same : (R ⟨e, k⟩ t).1 = some Event[i]) : k = i.castSucc := by
  unfold bankStackRight at same
  split at same
  · exact Fin.ext (nodup.getElem_inj_iff.mp (Option.some.inj same))
  · cases same

set_option maxHeartbeats 1800000 in
-- Each original marked arc belongs to a dependent gap type.
/-- The full fiber is a chain of arcs when all its seam classes are represented
by the endpoint pairs of one original stack. -/
theorem contractibleSpace_fiber_of_bank_stack_pairs {Y : Type*}
    (f : Realization X Banks → Y) (p : Y)
    (exact_glue : Exact X Banks) (nodup : ∀ e, (stack e).Nodup)
    (pair_class : ∀ (k : Fin (N + 1)) (z : Total X),
      Relation.EqvGen Banks (L ⟨e, k⟩ t) z ↔ z = L ⟨e, k⟩ t ∨ z = R ⟨e, k⟩ t)
    (seam_names : ∀ {a b : Total X}, Banks a b → f (Point a) = p →
      ∃ k : Fin (N + 1), a = L ⟨e, k⟩ t ∧ b = R ⟨e, k⟩ t)
    (vertex_fiber : ∀ i : Fin (N + 1), f (Point (L ⟨e, i⟩ t)) = p)
    (roof_fiber : ∀ x : X none, f (Point ⟨none, x⟩) = p → ∃ side, x = base e side t)
    (gap_fiber : ∀ g (x : X (some g)), f (Point ⟨some g, x⟩) = p → g ∈ stack e)
    (arcs : ∀ i : Fin N, ∃ P : Path (GapAt[i,false]) (GapAt[i,true]),
      Function.Injective P ∧ {x | f (Point ⟨some Event[i], x⟩) = p} = Set.range P) :
    ContractibleSpace {x | f x = p} := by
  classical
  let left (k : Fin (N + 1)) := L ⟨e, k⟩ t
  let right (k : Fin (N + 1)) := R ⟨e, k⟩ t
  have joined (k : Fin (N + 1)) : Point (left k) = Point (right k) :=
    point_eq_of_glue X (glue := Banks) ⟨⟨e, k⟩, t, rfl, rfl⟩
  let named (z : Total X) := ∃ k, z = left k ∨ z = right k
  have points_eq (a b : Total X) (eq : Point a = Point b) (inside : f (Point a) = p) :
      a = b ∨ ∃ k, (a = left k ∨ a = right k) ∧ (b = left k ∨ b = right k) := by
    have related := exact_glue a b eq
    by_cases known : named a
    · obtain ⟨k, at_k⟩ := known
      have orig := pair_class k b
      have a_eq : Relation.EqvGen Banks (left k) a :=
        (pair_class k a).mpr at_k
      exact Or.inr ⟨k, at_k, orig.mp (Relation.EqvGen.trans _ _ _ a_eq related)⟩
    · have preserved {x y : Total X} (h : Relation.EqvGen Banks x y) : x = a ↔ y = a := by
        induction h with
        | rel x y seam =>
          constructor
          · intro at_a
            have key : f (Point x) = p := (congrArg (fun z => f (Point z)) at_a).trans inside
            obtain ⟨k, hx, _⟩ := seam_names seam key
            exact (known ⟨k, Or.inl (at_a.symm.trans hx)⟩).elim
          · intro at_a
            have xy : Point x = Point y := point_eq_of_glue X seam
            have key : f (Point x) = p := (congrArg f xy).trans
              ((congrArg (fun z => f (Point z)) at_a).trans inside)
            obtain ⟨k, _, hy⟩ := seam_names seam key
            exact (known ⟨k, Or.inr (at_a.symm.trans hy)⟩).elim
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ hi hj => exact hi.trans hj
      exact Or.inl (((preserved related).mp rfl).symm)
  choose arc injective range_eq using arcs
  let vertex (k : Fin (N + 1)) := Point (left k)
  let tag (i : Fin N) (x : X (some Event[i])) : Total X := ⟨some Event[i], x⟩
  have left_rank {i : Fin N} {k : Fin (N + 1)} {x : X (some Event[i])}
      (same : tag i x = left k) : k = i.succ :=
    stackTags_at_left X stack base gap e t (nodup e) k i (congrArg Sigma.fst same.symm)
  have right_rank {i : Fin N} {k : Fin (N + 1)} {x : X (some Event[i])}
      (same : tag i x = right k) : k = i.castSucc :=
    stackTags_at_right X stack base gap e t (nodup e) k i (congrArg Sigma.fst same.symm)
  have first (i : Fin N) : vertex i.castSucc = Point (tag i GapAt[i,false]) :=
    (joined i.castSucc).trans (congrArg Point (bankStackRight_at X stack base gap e i t))
  have last (i : Fin N) : vertex i.succ = Point (tag i GapAt[i,true]) :=
    congrArg Point (bankStackLeft_after X stack base gap e i t)
  let graftArc (i : Fin N) : Path (vertex i.castSucc) (vertex i.succ) :=
    ((arc i).map ((of_lipschitz X Banks (some Event[i])).continuous)).cast (first i) (last i)
  have value (i : Fin N) (u : unitInterval) : graftArc i u = Point (tag i (arc i u)) := rfl
  have on_fiber (i : Fin N) (u : unitInterval) : f (graftArc i u) = p := by
    rw [value]
    have inside : arc i u ∈ {x | f (Point (tag i x)) = p} :=
      (range_eq i).symm ▸ Set.mem_range_self u
    exact inside
  have arc_injective (i : Fin N) : Function.Injective (graftArc i) := by
    intro u v eq
    have glued : Point (tag i (arc i u)) = Point (tag i (arc i v)) := eq
    have fiber : f (Point (tag i (arc i u))) = p := on_fiber i u
    apply injective i
    rcases points_eq _ _ glued fiber with same | ⟨k, h, h'⟩
    · exact eq_of_heq (Sigma.mk.inj same).2
    · rcases h with h | h <;> rcases h' with h' | h'
      · exact eq_of_heq (Sigma.mk.inj (h.trans h'.symm)).2
      · exact (Nat.succ_ne_self i.val (congrArg Fin.val ((left_rank h).symm.trans
          (right_rank h')))).elim
      · exact (Nat.succ_ne_self i.val (congrArg Fin.val ((left_rank h').symm.trans
          (right_rank h)))).elim
      · exact eq_of_heq (Sigma.mk.inj (h.trans h'.symm)).2
  have contacts (i j : Fin N) (ordered : i < j) :
      Set.range (graftArc i) ∩ Set.range (graftArc j) ⊆ {vertex j.castSucc} := by
    rintro z ⟨⟨u, at_z⟩, ⟨v, also⟩⟩
    have glue : Point (tag i (arc i u)) = Point (tag j (arc j v)) := at_z.trans also.symm
    have in_fiber : f (Point (tag i (arc i u))) = p := on_fiber i u
    rcases points_eq _ _ glue in_fiber with same | ⟨k, h, h'⟩
    · have named : Event[i] = Event[j] := Option.some.inj (congrArg Sigma.fst same)
      exact ((ne_of_lt ordered) ((List.nodup_iff_injective_get.mp (nodup e)) named)).elim
    rcases h with h | h <;> rcases h' with h' | h'
    · have same := congrArg Fin.val ((left_rank h).symm.trans (left_rank h'))
      change i.val + 1 = j.val + 1 at same
      have rank : i.val < j.val := ordered
      omega
    · have at_slot : z = vertex k := at_z.symm.trans (congrArg Point h)
      exact Set.mem_singleton_iff.mpr (at_slot.trans (congrArg vertex (right_rank h')))
    · have same := congrArg Fin.val ((right_rank h).symm.trans (left_rank h'))
      change i.val = j.val + 1 at same
      have rank : i.val < j.val := ordered
      omega
    · have same := congrArg Fin.val ((right_rank h).symm.trans (right_rank h'))
      change i.val = j.val at same
      have rank : i.val < j.val := ordered
      omega
  have whole : {x | f x = p} = Set.range vertex ∪ ⋃ i, Set.range (graftArc i) := by
    ext z
    constructor
    · intro inside
      obtain ⟨⟨tagged, x⟩, rfl⟩ := point_surjective X Banks z
      cases tagged with
      | none =>
        obtain ⟨side, at_bank⟩ := roof_fiber x inside
        subst x
        left
        cases side
        · exact ⟨0, congrArg Point (bankStackLeft_first X stack base gap e t)⟩
        · exact ⟨Fin.last N, (joined (Fin.last N)).trans
            (congrArg Point (bankStackRight_last X stack base gap e t))⟩
      | some g =>
        obtain ⟨i, named⟩ := List.get_of_mem (gap_fiber g x inside)
        subst g
        have fiber : x ∈ {y | f (Point ⟨some Event[i], y⟩) = p} := inside
        rw [range_eq i] at fiber
        obtain ⟨u, rfl⟩ := fiber
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, u, value i u⟩)
    · rintro (⟨i, rfl⟩ | member)
      · exact vertex_fiber i
      · obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp member
        exact on_fiber i u
  rw [whole]
  exact contractibleSpace_vertices_union_arcs vertex graftArc arc_injective contacts

/-- Over a strict physical point, the full fiber is the glued chain of its
exact individual gap arcs and the two original roof endpoints. -/
theorem contractibleSpace_fiber_of_single_bank_stack {Y : Type*}
    (f : Realization X Banks → Y) (p : Y)
    (exact_glue : Exact X Banks) (nodup : ∀ e, (stack e).Nodup)
    (unique : BankStackUniqueMarksAt stack X base gap e t)
    (on_stack : ∀ (slot : BankStackSlot stack) (s : Parameter slot.1),
      f (Point (L slot s)) = p →
        (⟨slot.1, s⟩ : Σ b, Parameter b) = ⟨e, t⟩)
    (vertex_fiber : ∀ i : Fin (N + 1), f (Point (L ⟨e, i⟩ t)) = p)
    (roof_fiber : ∀ x : X none, f (Point ⟨none, x⟩) = p → ∃ side, x = base e side t)
    (gap_fiber : ∀ g (x : X (some g)), f (Point ⟨some g, x⟩) = p → g ∈ stack e)
    (arcs : ∀ i : Fin N, ∃ P : Path (GapAt[i,false]) (GapAt[i,true]),
      Function.Injective P ∧ {x | f (Point ⟨some Event[i], x⟩) = p} = Set.range P) :
    ContractibleSpace {x | f x = p} := by
  apply contractibleSpace_fiber_of_bank_stack_pairs X stack base gap e t f p exact_glue nodup
    (fun k => bankStack_eqvGen_pair_iff stack X base gap nodup ⟨e, k⟩ t unique)
    ?_ vertex_fiber roof_fiber gap_fiber arcs
  intro a b joined inside
  obtain ⟨⟨w, k⟩, s, rfl, rfl⟩ := joined
  have time := on_stack ⟨w, k⟩ s inside
  have bank : w = e := congrArg Sigma.fst time
  subst w
  have parameter : s = t := eq_of_heq (Sigma.mk.inj time).2
  subst s
  exact ⟨k, rfl, rfl⟩

end Unfoldings.MetricGluing
