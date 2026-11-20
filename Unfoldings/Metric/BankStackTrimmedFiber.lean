module

public import Unfoldings.Metric.BankStackLocalClasses
public import Unfoldings.Topology.FiniteArcConcat
public import Mathlib.Data.List.Nodup

/-! A stack fiber with distinct seam points and possible final degenerate arcs. -/

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

variable {n : ℕ} (bound : n ≤ (stack e).length)

local notation "Kept[" i "]" => Fin.castLE bound i
local notation "Tag[" i "," x "]" => (Sigma.mk (some Event[Kept[i]]) x : Total X)
local notation "Vertex[" i "]" => Point (L (Sigma.mk e (Fin.castLE (Nat.succ_le_succ bound) i)) t)

/-- Outside the seam endpoints the equivalence relation has singleton classes. -/
private theorem eq_of_not_incident {x y : Total X} (equal : Relation.EqvGen Banks x y)
    (isolated : ∀ z, ¬ Banks x z ∧ ¬ Banks z x) : x = y := by
  have preserved {a b : Total X} (path : Relation.EqvGen Banks a b) : a = x ↔ b = x := by
    induction path with
    | rel a b h =>
      constructor
      · rintro rfl
        exact ((isolated b).1 h).elim
      · rintro rfl
        exact ((isolated a).2 h).elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hi hj => exact hi.trans hj
  exact ((preserved equal).mp rfl).symm

set_option maxHeartbeats 1950000 in
-- The marked arcs lie in distinct dependent piece types.
/-- If the remaining outgoing slots are distinct, the trimmed stack gives a
contractible full fiber. The omitted pieces must already lie at its vertices. -/
public theorem contractibleSpace_fiber_of_trimmed_bank_stack {Y : Type*}
    (f : Realization X Banks → Y) (p : Y)
    (exact_glue : Exact X Banks) (nodup : (stack e).Nodup)
    (distinct : Function.Injective (fun i : Fin (n + 1) => Vertex[i]))
    (vertex_fiber : ∀ i : Fin (n + 1), f (Vertex[i]) = p)
    (roof_fiber : ∀ x : X none, f (Point ⟨none, x⟩) = p →
      ∃ i : Fin (n + 1), Point ⟨none, x⟩ = Vertex[i])
    (gap_fiber : ∀ g (x : X (some g)), f (Point ⟨some g, x⟩) = p →
      (∃ i : Fin n, Event[Kept[i]] = g) ∨ (∃ i : Fin (n + 1), Point ⟨some g, x⟩ = Vertex[i]))
    (marked_seams : ∀ (i : Fin n) (x : X (some Event[Kept[i]])),
      f (Point Tag[i,x]) = p → (∃ y, Banks Tag[i,x] y ∨ Banks y Tag[i,x]) →
      x = GapAt[Kept[i],false] ∨ x = GapAt[Kept[i],true])
    (arcs : ∀ i : Fin n, ∃ P : Path (GapAt[Kept[i],false]) (GapAt[Kept[i],true]),
      Function.Injective P ∧ {x | f (Point Tag[i,x]) = p} = Set.range P) :
    ContractibleSpace {x | f x = p} := by
  classical
  choose arc arc_inj arc_range using arcs
  let vertex (k : Fin (n + 1)) := Vertex[k]
  have first (i : Fin n) : vertex i.castSucc = Point Tag[i,GapAt[Kept[i],false]] := by
    change Point (L ⟨e, (Kept[i]).castSucc⟩ t) = _
    have joined : Point (L ⟨e, (Kept[i]).castSucc⟩ t) = Point (R ⟨e, (Kept[i]).castSucc⟩ t) :=
      point_eq_of_glue X (glue := Banks) ⟨⟨e, (Kept[i]).castSucc⟩, t, rfl, rfl⟩
    exact joined.trans (congrArg Point (bankStackRight_at X stack base gap e Kept[i] t))
  have last (i : Fin n) : vertex i.succ = Point Tag[i,GapAt[Kept[i],true]] :=
    congrArg Point (bankStackLeft_after X stack base gap e Kept[i] t)
  let lift (i : Fin n) : Path (vertex i.castSucc) (vertex i.succ) :=
    ((arc i).map ((of_lipschitz X Banks (some Event[Kept[i]])).continuous)).cast (first i) (last i)
  have at_point (i : Fin n) (u : unitInterval) : lift i u = Point Tag[i,arc i u] := rfl
  have inside (i : Fin n) (u : unitInterval) : f (Point Tag[i,arc i u]) = p := by
    have h : arc i u ∈ {x | f (Point Tag[i,x]) = p} :=
      (arc_range i).symm ▸ Set.mem_range_self u
    exact h
  have other_piece (i j : Fin n) (u v : unitInterval)
      (equal : lift i u = lift j v) (different : Tag[i,arc i u] ≠ Tag[j,arc j v]) :
      (arc i u = GapAt[Kept[i],false] ∨ arc i u = GapAt[Kept[i],true]) ∧
      (arc j v = GapAt[Kept[j],false] ∨ arc j v = GapAt[Kept[j],true]) := by
    have related := exact_glue _ _ equal
    constructor
    · apply marked_seams i _ (inside i u)
      by_contra hn
      apply different
      exact eq_of_not_incident X stack base gap related (fun y =>
        ⟨fun h => hn ⟨y, Or.inl h⟩, fun h => hn ⟨y, Or.inr h⟩⟩)
    · apply marked_seams j _ (inside j v)
      by_contra hn
      apply different
      exact (eq_of_not_incident X stack base gap (Relation.EqvGen.symm _ _ related) (fun y =>
        ⟨fun h => hn ⟨y, Or.inl h⟩, fun h => hn ⟨y, Or.inr h⟩⟩)).symm
  have endpoint_rank (i : Fin n) (u : unitInterval)
      (named : arc i u = GapAt[Kept[i],false] ∨ arc i u = GapAt[Kept[i],true]) :
      lift i u = vertex i.castSucc ∨ lift i u = vertex i.succ := by
    change Point Tag[i,arc i u] = _ ∨ Point Tag[i,arc i u] = _
    rcases named with h | h
    · exact Or.inl ((congrArg (fun x => Point Tag[i,x]) h).trans (first i).symm)
    · exact Or.inr ((congrArg (fun x => Point Tag[i,x]) h).trans (last i).symm)
  have injective (i : Fin n) : Function.Injective (lift i) := by
    intro u v equal
    apply arc_inj i
    by_cases same : Tag[i,arc i u] = Tag[i,arc i v]
    · exact eq_of_heq (Sigma.mk.inj same).2
    obtain ⟨h, g⟩ := other_piece i i u v equal same
    rcases h with h | h <;> rcases g with g | g
    · exact h.trans g.symm
    · have h' : lift i u = vertex i.castSucc :=
        (congrArg (fun x => Point Tag[i,x]) h).trans (first i).symm
      have g' : lift i v = vertex i.succ :=
        (congrArg (fun x => Point Tag[i,x]) g).trans (last i).symm
      exact (Nat.ne_of_lt (Nat.lt_succ_self i.val)
        (congrArg Fin.val (distinct (h'.symm.trans (equal.trans g'))))).elim
    · have h' : lift i u = vertex i.succ :=
        (congrArg (fun x => Point Tag[i,x]) h).trans (last i).symm
      have g' : lift i v = vertex i.castSucc :=
        (congrArg (fun x => Point Tag[i,x]) g).trans (first i).symm
      exact (Nat.ne_of_lt (Nat.lt_succ_self i.val)
        (congrArg Fin.val (distinct (g'.symm.trans (equal.symm.trans h'))))).elim
    · exact h.trans g.symm
  have contacts (i j : Fin n) (ordered : i < j) :
      Set.range (lift i) ∩ Set.range (lift j) ⊆ {vertex j.castSucc} := by
    rintro z ⟨⟨u, at_z⟩, ⟨v, also⟩⟩
    have equal := at_z.trans also.symm
    have different : Tag[i,arc i u] ≠ Tag[j,arc j v] := by
      intro h
      have events := Option.some.inj (congrArg Sigma.fst h)
      have registers := List.nodup_iff_injective_get.mp nodup events
      exact (ne_of_lt ordered) (Fin.ext (congrArg (fun k : Fin N => k.val) registers))
    obtain ⟨h, g⟩ := other_piece i j u v equal different
    have rank : i.val < j.val := ordered
    rcases endpoint_rank j v g with before | after
    · exact Set.mem_singleton_iff.mpr (also.symm.trans before)
    · rcases endpoint_rank i u h with origin | finish
      · have h := congrArg Fin.val (distinct (origin.symm.trans (equal.trans after)))
        change i.val = j.val + 1 at h
        omega
      · have h := congrArg Fin.val (distinct (finish.symm.trans (equal.trans after)))
        change i.val + 1 = j.val + 1 at h
        omega
  have whole : {x | f x = p} = Set.range vertex ∪ ⋃ i, Set.range (lift i) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨name, x⟩, rfl⟩ := point_surjective X Banks z
      cases name with
      | none =>
        obtain ⟨i, hi⟩ := roof_fiber x hz
        exact Or.inl ⟨i, hi.symm⟩
      | some g =>
        rcases gap_fiber g x hz with ⟨i, rfl⟩ | ⟨i, hi⟩
        · have mem : x ∈ {y | f (Point Tag[i,y]) = p} := hz
          rw [arc_range i] at mem
          obtain ⟨u, rfl⟩ := mem
          exact Or.inr (Set.mem_iUnion.mpr ⟨i, u, at_point i u⟩)
        · exact Or.inl ⟨i, hi.symm⟩
    · rintro (⟨i, rfl⟩ | h)
      · exact vertex_fiber i
      · obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp h
        exact inside i u
  rw [whole]
  exact contractibleSpace_vertices_union_arcs vertex lift injective contacts

end Unfoldings.MetricGluing
