module

public import Unfoldings.Metric.Route
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Route metrics for a family of spaces with declared identifications

Within-piece motion has its original cost. A declared identification can be
traversed in either direction at zero cost. All other direct jumps cost infinity.
Route distance constructs the pseudometric, and its separation quotient gives
an extended metric space. For arbitrary identifications the quotient can make
additional zero-distance identifications; exactness for finite triangle
complexes is a subsequent theorem, not an assumption here.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]

/-- Points in their original cells, before any identifications. -/
abbrev Total := Σ i, E i

/-- Direct movement inside a single cell; other jumps are forbidden. -/
noncomputable def faceCost (a b : Total E) : ℝ≥0∞ := by
  classical
  exact match a, b with
    | ⟨i, x⟩, ⟨j, y⟩ => if h : i = j then edist (h ▸ x) y else ⊤

theorem faceCost_comm (x y : Total E) : faceCost E x y = faceCost E y x := by
  classical
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  by_cases same : i = j
  · subst j
    simp [faceCost, edist_comm]
  · simp [faceCost, same, Ne.symm same]

/-- Seams are undirected even when their input relation lists only one orientation. -/
noncomputable def stepCost (glue : Total E → Total E → Prop) (x y : Total E) : ℝ≥0∞ := by
  classical
  exact if glue x y ∨ glue y x then 0 else faceCost E x y

theorem stepCost_comm (glue : Total E → Total E → Prop) (x y : Total E) :
    stepCost E glue x y = stepCost E glue y x := by
  classical
  simp only [stepCost, or_comm (a := glue x y), faceCost_comm E x y]

theorem stepCost_le_faceCost (glue : Total E → Total E → Prop) (x y : Total E) :
    stepCost E glue x y ≤ faceCost E x y := by
  classical
  unfold stepCost
  split <;> simp

/-- More identifications can only reduce the step costs. -/
theorem stepCost_antitone {R S : Total E → Total E → Prop}
    (inclusion : ∀ x y, R x y → S x y) (x y : Total E) :
    stepCost E S x y ≤ stepCost E R x y := by
  classical
  by_cases related : R x y ∨ R y x
  · have related' : S x y ∨ S y x := related.imp (inclusion x y) (inclusion y x)
    simp [stepCost, related, related']
  · simp only [stepCost, ite_eq_right related]
    exact stepCost_le_faceCost E S x y

/-- A separate type carrying the constructed route pseudometric, not a sigma metric. -/
def PreSpace (_glue : Total E → Total E → Prop) := Total E

noncomputable instance (glue : Total E → Total E → Prop) :
    PseudoEMetricSpace (PreSpace E glue) :=
  Route.pseudoEMetricSpace (stepCost E glue) (stepCost_comm E glue)

/-- Quotienting zero route distances produces a genuine extended metric space. -/
abbrev Realization (glue : Total E → Total E → Prop) :=
  SeparationQuotient (PreSpace E glue)

/-- The image of a point with its cell tag. -/
def point (glue : Total E → Total E → Prop) (x : Total E) : Realization E glue :=
  SeparationQuotient.mk (x : PreSpace E glue)

/-- The canonical map from one original cell. -/
def of (glue : Total E → Total E → Prop) (i : ι) (x : E i) : Realization E glue :=
  point E glue ⟨i, x⟩

@[simp] theorem edist_point (glue : Total E → Total E → Prop) (x y : Total E) :
    edist (point E glue x) (point E glue y) = Route.distance (stepCost E glue) x y := rfl

theorem edist_of_le (glue : Total E → Total E → Prop) (i : ι) (x y : E i) :
    edist (of E glue i x) (of E glue i y) ≤ edist x y := by
  exact (Route.distance_le_cost _ _ _).trans
    ((stepCost_le_faceCost E glue ⟨i, x⟩ ⟨i, y⟩).trans_eq (by simp [faceCost]))

/-- Gluing may create shortcuts; nonexpansion is the unconditional face-map theorem. -/
theorem of_lipschitz (glue : Total E → Total E → Prop) (i : ι) :
    LipschitzWith 1 (of E glue i) := LipschitzWith.of_edist_le (edist_of_le E glue i)

theorem point_eq_of_glue {glue : Total E → Total E → Prop} {x y : Total E}
    (related : glue x y) : point E glue x = point E glue y := by
  classical
  apply edist_eq_zero.mp
  rw [edist_point]
  exact le_antisymm ((Route.distance_le_cost _ x y).trans_eq
    (by simp [stepCost, related])) bot_le

/-- Route distance bounds the distance of any compatible nonexpanding images. -/
theorem map_edist_le {Y : Type*} [PseudoEMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) (x y : Total E) :
    edist (f x.1 x.2) (f y.1 y.2) ≤ Route.distance (stepCost E glue) x y := by
  classical
  refine Route.le_distance (stepCost E glue)
    (fun (a b : Total E) => edist (f a.1 a.2) (f b.1 b.2))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _) ?_ x y
  intro a b
  by_cases related : glue a b ∨ glue b a
  · have equal : f a.1 a.2 = f b.1 b.2 :=
      related.elim (compatible a b) (fun h => (compatible b a h).symm)
    simp [stepCost, related, equal]
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    by_cases same : i = j
    · subst j
      simpa [stepCost, related, faceCost] using (nonexpanding i).edist_le_mul a b
    · simp [stepCost, related, faceCost, same]

/-- Descend compatible nonexpanding maps to the metric realization. -/
noncomputable def lift {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) : Realization E glue → Y :=
  SeparationQuotient.lift (fun x : PreSpace E glue => f x.1 x.2) (by
    intro x y inseparable
    apply edist_eq_zero.mp
    exact le_antisymm ((map_edist_le E glue f nonexpanding compatible x y).trans_eq
      (EMetric.inseparable_iff.mp inseparable)) bot_le)

@[simp] theorem lift_point {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) (x : Total E) :
    lift E glue f nonexpanding compatible (point E glue x) = f x.1 x.2 := rfl

theorem lift_lipschitz {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2) :
    LipschitzWith 1 (lift E glue f nonexpanding compatible) := by
  apply LipschitzWith.of_edist_le
  intro a b
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  exact map_edist_le E glue f nonexpanding compatible x y

theorem lift_unique {Y : Type*} [EMetricSpace Y]
    (glue : Total E → Total E → Prop) (f : ∀ i, E i → Y)
    (nonexpanding : ∀ i, LipschitzWith 1 (f i))
    (compatible : ∀ x y, glue x y → f x.1 x.2 = f y.1 y.2)
    (g : Realization E glue → Y) (agrees : ∀ i x, g (of E glue i x) = f i x) :
    g = lift E glue f nonexpanding compatible := by
  funext a
  obtain ⟨⟨i, x⟩, rfl⟩ := SeparationQuotient.surjective_mk a
  exact agrees i x

/-- Identifying additional seams cannot increase route distance. -/
theorem distance_antitone {R S : Total E → Total E → Prop}
    (inclusion : ∀ x y, R x y → S x y) (x y : Total E) :
    Route.distance (stepCost E S) x y ≤ Route.distance (stepCost E R) x y :=
  Route.distance_mono (stepCost_antitone E inclusion) x y

/-- The canonical nonexpanding map that forgets cuts. -/
noncomputable def forget {R S : Total E → Total E → Prop}
    (inclusion : ∀ x y, R x y → S x y) : Realization E R → Realization E S :=
  lift E R (of E S) (of_lipschitz E S)
    (fun x y h => point_eq_of_glue E (inclusion x y h))

@[simp] theorem forget_point {R S : Total E → Total E → Prop}
    (inclusion : ∀ x y, R x y → S x y) (x : Total E) :
    forget E inclusion (point E R x) = point E S x := rfl

theorem forget_lipschitz {R S : Total E → Total E → Prop}
    (inclusion : ∀ x y, R x y → S x y) : LipschitzWith 1 (forget E inclusion) :=
  lift_lipschitz E R (of E S) (of_lipschitz E S)
    (fun x y h => point_eq_of_glue E (inclusion x y h))

end Unfoldings.MetricGluing
