module

public import Unfoldings.Topology.ContractibleLift
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! A section of a covering along a compact fiber extends over a neighborhood. -/

@[expose] public section

noncomputable section

open Set Topology Filter

namespace Unfoldings

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {p : E → X}

/-- A local homeomorphism injective on a compact set remains injective on an
open neighborhood of that set. -/
theorem IsLocalHomeomorph.exists_injOn_open_of_compact
    (local_homeo : IsLocalHomeomorph p) {K : Set E} (compact : IsCompact K)
    (injective : InjOn p K) : ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ InjOn p U := by
  let good : Set (E × E) := {a | p a.1 = p a.2 → a.1 = a.2}
  have open_good : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, y⟩ member
    by_cases equal : p x = p y
    · have same : x = y := member equal
      subst y
      obtain ⟨e, at_x, name⟩ := local_homeo x
      apply Filter.mem_of_superset ((e.open_source.prod e.open_source).mem_nhds ⟨at_x, at_x⟩)
      rintro ⟨a, b⟩ ⟨ha, hb⟩ eq
      exact e.injOn ha hb (by rw [← name]; exact eq)
    · have open_unequal : IsOpen {a : E × E | p a.1 ≠ p a.2} :=
        (isClosed_eq (local_homeo.continuous.comp continuous_fst)
          (local_homeo.continuous.comp continuous_snd)).isOpen_compl
      exact Filter.mem_of_superset (open_unequal.mem_nhds equal)
        (fun _ different h => (different h).elim)
  have contained : K ×ˢ K ⊆ good := fun a ha => injective ha.1 ha.2
  obtain ⟨U, V, open_U, open_V, in_U, in_V, safe⟩ :=
    generalized_tube_lemma compact compact open_good contained
  refine ⟨U ∩ V, open_U.inter open_V, fun _ h => ⟨in_U h, in_V h⟩, ?_⟩
  intro x hx y hy eq
  exact (safe (show (x, y) ∈ U ×ˢ V from ⟨hx.1, hy.2⟩)) eq

/-- A continuous section on a compact subset extends to a section on an open
neighborhood of that subset. -/
theorem exists_localHomeomorph_section_near_compact [Nonempty E]
    (local_homeo : IsLocalHomeomorph p)
    {K : Set X} (compact : IsCompact K) (s : C(K, E))
    (projects : ∀ x : K, p (s x) = x.val) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ t : C(V, E),
      (∀ y : V, p (t y) = y.val) ∧ ∀ x : K, ∃ hx : x.val ∈ V, t ⟨x.val, hx⟩ = s x := by
  have compact_image : IsCompact (Set.range s) := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp compact
    exact isCompact_range s.continuous
  have injective : InjOn p (Set.range s) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact congrArg s (Subtype.ext ((projects x).symm.trans (h.trans (projects y))))
  obtain ⟨U, open_U, contains, unique⟩ :=
    IsLocalHomeomorph.exists_injOn_open_of_compact local_homeo compact_image injective
  let e := OpenPartialHomeomorph.ofContinuousOpen (unique.toPartialEquiv p U)
    local_homeo.continuous.continuousOn local_homeo.isOpenMap open_U
  have f_eq : ∀ a, e a = p a := fun _ => rfl
  have hK : K ⊆ e.target := by
    intro x hx
    change x ∈ p '' U
    let a : K := ⟨x, hx⟩
    have in_range : s a ∈ Set.range s := ⟨a, rfl⟩
    exact ⟨s a, contains in_range, projects a⟩
  let t : C(e.target, E) := ⟨fun a => e.symm a.val,
    continuousOn_iff_continuous_domRestrict.mp e.continuousOn_invFun⟩
  refine ⟨e.target, e.open_target, hK, t, ?_, ?_⟩
  · intro x
    exact (f_eq _).symm.trans (e.right_inv x.property)
  · intro x
    refine ⟨hK x.property, ?_⟩
    change e.symm x.val = s x
    rw [← projects x, ← f_eq (s x)]
    exact e.left_inv (contains (Set.mem_range_self x))

/-- Over a proper map with a contractible fiber, a covering section exists on
the entire preimage of some open neighborhood of the fiber value. -/
theorem exists_covering_section_near_proper_fiber (f : X → Y) (proper : IsProperMap f)
    (p : E → X) (covering : IsCoveringMap p) (onto : Function.Surjective p) (y : Y)
    (contractible : ContractibleSpace (f ⁻¹' {y})) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∃ s : C(f ⁻¹' U, E), ∀ a, p (s a) = a.val := by
  let K := f ⁻¹' {y}
  let : ContractibleSpace K := contractible
  have compact : IsCompact K := proper.isCompact_preimage isCompact_singleton
  obtain ⟨lift, equation⟩ := exists_covering_lift_of_contractible p covering onto
    (⟨Subtype.val, continuous_subtype_val⟩ : C(K, X))
  let : Nonempty E := ⟨lift (Classical.choice inferInstance)⟩
  obtain ⟨V, open_V, contains, t, projects, _⟩ :=
    exists_localHomeomorph_section_near_compact covering.isLocalHomeomorph compact lift
      (fun x => congrFun equation x)
  let U := (f '' Vᶜ)ᶜ
  have open_U : IsOpen U := (proper.isClosedMap _ open_V.isClosed_compl).isOpen_compl
  have at_y : y ∈ U := by
    rintro ⟨x, hx, eq⟩
    exact hx (contains eq)
  have inside : f ⁻¹' U ⊆ V := by
    intro x hx
    by_contra absent
    exact hx ⟨x, absent, rfl⟩
  let embed : C(f ⁻¹' U, V) :=
    ⟨fun a => ⟨a.val, inside a.property⟩, continuous_subtype_val.subtype_mk _⟩
  exact ⟨U, open_U, at_y, t.comp embed, fun a => projects (embed a)⟩

omit [T2Space X] in
/-- A continuous transition into a totally disconnected space descends through
a quotient with preconnected fibers. -/
theorem exists_descend_continuous_of_preconnected_fibers {D : Type*}
    [TopologicalSpace D] [TotallyDisconnectedSpace D] (f : X → Y) (q : IsQuotientMap f)
    (fibers : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) (g : C(X, D)) :
    ∃ c : C(Y, D), c ∘ f = g := by
  let k (y : Y) := (q.surjective y).choose
  let t (y : Y) := g (k y)
  have evaluate : t ∘ f = g := by
    funext x
    have h : f (k (f x)) = f x := (q.surjective (f x)).choose_spec
    have one := ((fibers (f x)).image g g.continuous.continuousOn).subsingleton
    exact one ⟨k (f x), h, rfl⟩ ⟨x, rfl, rfl⟩
  have continuous : Continuous t := q.continuous_iff.mpr (evaluate.symm ▸ g.continuous)
  exact ⟨⟨t, continuous⟩, evaluate⟩

end Unfoldings
