module

public import Unfoldings.FewestNets.IcosahedronEdgeIncidence

/-! Each fine triangle is incident to its three distinct primal edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

def siteOfCorner {q : ℕ} (t : MeshFace q) (k : Fin 3) : meshSites q :=
  ⟨inscribedCorners t k, ⟨(t, k), rfl⟩⟩

theorem siteOfCorner_injective {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    Function.Injective (siteOfCorner t) :=
  fun _ _ eq => (linearIndependent_inscribedCorners hq t).injective (congrArg Subtype.val eq)

private theorem fin_three_other_iff (i k : Fin 3) : i = k + 1 ∨ i = k + 2 ↔ i ≠ k := by
  have table : ∀ i k : Fin 3, i = k + 1 ∨ i = k + 2 ↔ i ≠ k := by decide +kernel
  exact table i k

theorem fin_three_pair_complement (i j k : Fin 3) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    (i = k + 1 ∧ j = k + 2) ∨ (i = k + 2 ∧ j = k + 1) := by
  have table : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (i = k + 1 ∧ j = k + 2) ∨ (i = k + 2 ∧ j = k + 1) := by decide +kernel
  exact table i j k ij ik jk

def edgeOpposite {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) : MeshEdge q := by
  classical
  have different : k + 1 ≠ k + 2 := by
    have table : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide +kernel
    exact table k
  refine ⟨{siteOfCorner t (k + 1), siteOfCorner t (k + 2)},
    Finset.card_eq_two.mpr ⟨_, _, (siteOfCorner_injective hq t).ne different, rfl⟩, t, ?_⟩
  intro a ha
  rw [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact Set.mem_range_self (k + 1)
  · exact Set.mem_range_self (k + 2)

theorem edgeOpposite_incident {q : ℕ} (hq : 0 < q) (t : MeshFace q) (k : Fin 3) :
    EdgeIncident (edgeOpposite hq t k) t := by
  classical
  intro a ha
  change a ∈ ({siteOfCorner t (k + 1), siteOfCorner t (k + 2)} : Finset (meshSites q)) at ha
  rw [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact Set.mem_range_self (k + 1)
  · exact Set.mem_range_self (k + 2)

theorem site_mem_edgeOpposite_iff {q : ℕ} (hq : 0 < q) (t : MeshFace q) (i k : Fin 3) :
    siteOfCorner t i ∈ (edgeOpposite hq t k).val ↔ i ≠ k := by
  classical
  change siteOfCorner t i ∈ ({siteOfCorner t (k + 1), siteOfCorner t (k + 2)}
    : Finset (meshSites q)) ↔ _
  rw [Finset.mem_insert, Finset.mem_singleton, (siteOfCorner_injective hq t).eq_iff,
    (siteOfCorner_injective hq t).eq_iff]
  exact fin_three_other_iff i k

/-- The three edges of one triangle are indexed by their omitted corners. -/
def faceIncidentEquivCorners {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    {e : MeshEdge q // EdgeIncident e t} ≃ Fin 3 := by
  classical
  refine (Equiv.ofBijective (fun k => ⟨edgeOpposite hq t k, edgeOpposite_incident hq t k⟩) ?_).symm
  constructor
  · intro i j eq
    by_contra other
    have equal : edgeOpposite hq t i = edgeOpposite hq t j := congrArg Subtype.val eq
    have right := (site_mem_edgeOpposite_iff hq t i j).mpr other
    rw [← equal] at right
    exact (site_mem_edgeOpposite_iff hq t i i).mp right rfl
  · rintro ⟨e, he⟩
    obtain ⟨a, b, different, pair⟩ := meshEdge_has_vertices e
    have ha : a ∈ e.val := by rw [pair]; simp
    have hb : b ∈ e.val := by rw [pair]; simp
    obtain ⟨i, hi⟩ := he a ha
    obtain ⟨j, hj⟩ := he b hb
    have hi' : siteOfCorner t i = a := Subtype.ext hi
    have hj' : siteOfCorner t j = b := Subtype.ext hj
    have ij : i ≠ j := fun eq =>
      different (hi'.symm.trans ((congrArg (siteOfCorner t) eq).trans hj'))
    obtain ⟨k, ik, jk, _⟩ := exists_fin_three_rest i j ij
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    change ({siteOfCorner t (k + 1), siteOfCorner t (k + 2)} : Finset (meshSites q)) = e.val
    rw [pair, ← hi', ← hj']
    rcases fin_three_pair_complement i j k ij ik jk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Finset.pair_comm _ _

theorem card_faceIncident {q : ℕ} (hq : 0 < q) (t : MeshFace q) :
    Nat.card {e : MeshEdge q // EdgeIncident e t} = 3 := by
  rw [Nat.card_congr (faceIncidentEquivCorners hq t), Nat.card_fin]

end Unfoldings.FewestNets.Icosahedron
