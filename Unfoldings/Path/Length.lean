module

public import Mathlib.Topology.Path
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Extended length of continuous paths

Length is Mathlib total variation on the unit interval. It is defined for
arbitrary extended pseudometric targets, including disconnected cut surfaces.
The extension and concatenation proofs adapt the variation arguments in
slef/EdgeUnfoldings, snapshot 56caca8cdc44dbc2f839e93808088d56ea3f0780,
`ArcLength.lean`, `SurfacePathJoining.lean`, and `SurfacePathReversal.lean`.
They do not depend on an embedded convex polyhedron.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace Path

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {a b c : X}

/-- Arc length, possibly infinite, measured by total variation on the unit interval. -/
noncomputable def eLength (p : Path a b) : ℝ≥0∞ := eVariationOn p Set.univ

/-- No continuous path with the same endpoints has smaller arc length. -/
def IsLengthMinimizing (p : Path a b) : Prop := ∀ q : Path a b, p.eLength ≤ q.eLength

theorem edist_le_eLength (p : Path a b) : edist a b ≤ p.eLength := by
  change edist a b ≤ eVariationOn p Set.univ
  simpa only [Path.source, Path.target] using
    eVariationOn.edist_le p (Set.mem_univ (0 : unitInterval)) (Set.mem_univ (1 : unitInterval))

theorem edist_apply_le_eLength (p : Path a b) (s t : unitInterval) :
    edist (p s) (p t) ≤ p.eLength := eVariationOn.edist_le p (mem_univ s) (mem_univ t)

/-- The clamped real-parameter extension has the same variation as the original path. -/
theorem eLength_eq_extend (p : Path a b) : p.eLength = eVariationOn p.extend (Set.Icc 0 1) := by
  have restriction : p.extend ∘ ((↑) : unitInterval → ℝ) = p := by
    funext t
    exact p.extend_apply t.property
  have image : ((↑) : unitInterval → ℝ) '' Set.univ = Set.Icc 0 1 := by ext t; simp
  rw [eLength, ← image, ← eVariationOn.comp_eq_of_monotoneOn _ _
    (show MonotoneOn ((↑) : unitInterval → ℝ) Set.univ from fun _ _ _ _ h => h), restriction]

@[simp] theorem eLength_refl (a : X) : (Path.refl a).eLength = 0 := by
  apply eVariationOn.constant_on
  rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
  rfl

@[simp] theorem eLength_symm (p : Path a b) : p.symm.eLength = p.eLength := by
  change eVariationOn (p ∘ unitInterval.symm) Set.univ = eVariationOn p Set.univ
  rw [eVariationOn.comp_eq_of_antitoneOn _ _
    (unitInterval.strictAnti_symm.antitone.antitoneOn Set.univ),
    image_univ, unitInterval.symm_bijective.surjective.range_eq]

theorem IsLengthMinimizing.symm {p : Path a b} (minimal : p.IsLengthMinimizing) :
    p.symm.IsLengthMinimizing := by
  intro q
  simpa only [eLength_symm] using minimal q.symm

/-- Concatenation adds lengths even when a path has infinite length. -/
@[simp] theorem eLength_trans (p : Path a b) (q : Path b c) :
    (p.trans q).eLength = p.eLength + q.eLength := by
  rw [eLength_eq_extend, eLength_eq_extend, eLength_eq_extend]
  have split := eVariationOn.Icc_add_Icc (p.trans q).extend
    (s := Set.univ) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (mem_univ _)
  simp only [univ_inter] at split
  rw [← split]
  have left : EqOn (p.trans q).extend (p.extend ∘ (fun t : ℝ => 2 * t)) (Icc 0 (1 / 2)) :=
    fun _ ht => Path.extend_trans_of_le_half _ _ ht.2
  have right : EqOn (p.trans q).extend (q.extend ∘ (fun t : ℝ => 2 * t - 1)) (Icc (1 / 2) 1) :=
    fun _ ht => Path.extend_trans_of_half_le _ _ ht.1
  rw [eVariationOn.congr left, eVariationOn.congr right,
    eVariationOn.comp_eq_of_monotoneOn _ _ (by intro x hx y hy h; dsimp; linarith),
    eVariationOn.comp_eq_of_monotoneOn _ _ (by intro x hx y hy h; dsimp; linarith)]
  have left_image : (fun t : ℝ => 2 * t) '' Icc 0 (1 / 2) = Icc 0 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      constructor <;> linarith [hu.1, hu.2]
    · intro ht
      exact ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  have right_image : (fun t : ℝ => 2 * t - 1) '' Icc (1 / 2) 1 = Icc 0 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      constructor <;> linarith [hu.1, hu.2]
    · intro ht
      exact ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  rw [left_image, right_image]

theorem eLength_map_le (p : Path a b) {f : X → Y} {K : ℝ≥0} (lipschitz : LipschitzWith K f) :
    (p.map lipschitz.continuous).eLength ≤ K * p.eLength := by
  change eVariationOn (f ∘ p) Set.univ ≤ K * eVariationOn p Set.univ
  exact lipschitz.lipschitzOnWith.comp_eVariationOn_le (fun _ _ => Set.mem_univ _)

/-- Isometries preserve the full length of a path. -/
theorem eLength_map_isometry (p : Path a b) {f : X → Y} (isometry : Isometry f) :
    (p.map isometry.continuous).eLength = p.eLength := by
  change eVariationOn (f ∘ p) Set.univ = eVariationOn p Set.univ
  have same (x y : unitInterval) : edist (f (p x)) (f (p y)) = edist (p x) (p y) :=
    isometry _ _
  simp only [eVariationOn, Function.comp_apply, same]

/-- A uniform speed bound on the unit interval bounds total length. -/
theorem eLength_le_of_lipschitz (p : Path a b) {K : ℝ≥0} (speed : LipschitzWith K p) :
    p.eLength ≤ K := by
  have unit : eVariationOn (id : unitInterval → unitInterval) Set.univ ≤ 1 := by
    have same := eVariationOn.comp_eq_of_monotoneOn (id : ℝ → ℝ)
      ((↑) : unitInterval → ℝ) (show MonotoneOn ((↑) : unitInterval → ℝ) Set.univ
        from fun _ _ _ _ h => h)
    have distance : eVariationOn (id : unitInterval → unitInterval) Set.univ =
        eVariationOn ((↑) : unitInterval → ℝ) Set.univ := rfl
    rw [distance]
    have image : ((↑) : unitInterval → ℝ) '' Set.univ = Set.Icc 0 1 := by ext t; simp
    change eVariationOn ((id : ℝ → ℝ) ∘ ((↑) : unitInterval → ℝ)) Set.univ ≤ 1
    rw [same, image]
    simp
  have bound := speed.lipschitzOnWith.comp_eVariationOn_le
    (show MapsTo (id : unitInterval → unitInterval) Set.univ Set.univ from fun _ _ => mem_univ _)
  exact bound.trans (by simpa using mul_le_mul_right unit (K : ℝ≥0∞))

end Path
