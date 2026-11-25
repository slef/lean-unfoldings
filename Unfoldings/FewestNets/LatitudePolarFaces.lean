module

public import Unfoldings.FewestNets.LatitudeNorthFanSupport
public import Unfoldings.FewestNets.LatitudeAnnularFaces

/-! The literal polar fan triangles lie on the boundary of the same sampled convex hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

theorem latitudeColatitude_reflect {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j ≤ latitudeStripCount a) :
    latitudeColatitude a (latitudeStripCount a - j) = π - latitudeColatitude a j := by
  have total := latitudeColatitude_last positive small
  unfold latitudeColatitude at total ⊢
  rw [Nat.cast_sub valid, sub_mul]
  linarith only [total]

theorem latitudeRowSize_reflect {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j ≤ latitudeStripCount a) :
    latitudeRowSize a (latitudeStripCount a - j) = latitudeRowSize a j := by
  unfold latitudeRowSize
  rw [latitudeColatitude_reflect positive small valid, sin_pi_sub]

theorem latitudeSite_inner_reflect (ell row longitude longitude' : ℝ) :
    inner ℝ (latitudeSite (π - ell) longitude) (latitudeSite (π - row) longitude') =
      inner ℝ (latitudeSite ell longitude) (latitudeSite row longitude') := by
  let w := longitude' - longitude
  have left := latitudeSite_inner (π - ell) (π - row) longitude w
  have right := latitudeSite_inner ell row longitude w
  have mem : longitude + w = longitude' := by dsimp only [w]; ring
  rw [mem, sin_pi_sub, sin_pi_sub, show π - row - (π - ell) = -(row - ell) by ring,
    cos_neg] at left
  rw [mem] at right
  exact left.trans right.symm

theorem latitudeRowSite_inner_reflect {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j ≤ latitudeStripCount a) (ell longitude : ℝ) (k : ℕ) :
    inner ℝ (latitudeSite (π - ell) longitude) (latitudeRowSite a (latitudeStripCount a - j) k) =
      inner ℝ (latitudeSite ell longitude) (latitudeRowSite a j k) := by
  unfold latitudeRowSite
  rw [latitudeRowSize_reflect positive small valid, latitudeColatitude_reflect positive small valid]
  exact latitudeSite_inner_reflect ell (latitudeColatitude a j) longitude _

/-- The northern polar triangle with these three sampled vertices. -/
def latitudeNorthChordTriangle (a : ℝ) (edge : Fin (latitudeRowSize a 0)) : Set Space :=
  convexHull ℝ {latitudeSite 0 0, latitudeRowSite a 0 edge.val,
    latitudeRowSite a 0 (edge.val + 1)}

/-- The southern polar triangle is indexed by the reflected northern edge. -/
def latitudeSouthChordTriangle (a : ℝ) (edge : Fin (latitudeRowSize a 0)) : Set Space :=
  convexHull ℝ {latitudeSite π 0, latitudeRowSite a (latitudeStripCount a) edge.val,
    latitudeRowSite a (latitudeStripCount a) (edge.val + 1)}

theorem latitudeNorthChordTriangle_subset_frontier {a : ℝ} (positive : 0 < a)
    (small : a ≤ π / 6) (edge : Fin (latitudeRowSize a 0)) :
    latitudeNorthChordTriangle a edge ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  obtain ⟨θ, _, _, _, pole, left, right, upper, south⟩ :=
    exists_latitudeNorthFan_support positive small edge
  let longitude := rowMidpoint (latitudeRowSize a 0) edge
  unfold latitudeNorthChordTriangle
  refine convexHull_subset_frontier_of_latitudeSupport ?_ θ longitude (cos θ) ?_ ?_
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (Set.mem_insert _ _)
    · exact latitudeRowSite_mem_sites a (Nat.zero_le _) _
    · exact latitudeRowSite_mem_sites a (Nat.zero_le _) _
  · intro p hp
    rcases hp with poles | ⟨i, valid, k, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at poles
      rcases poles with rfl | rfl
      · exact pole.le
      · exact south.le
    · exact upper i valid k
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact pole
    · exact left
    · exact right

theorem latitudeSouthChordTriangle_subset_frontier {a : ℝ} (positive : 0 < a)
    (small : a ≤ π / 6) (edge : Fin (latitudeRowSize a 0)) :
    latitudeSouthChordTriangle a edge ⊆ frontier (convexHull ℝ (latitudeSites a)) := by
  obtain ⟨θ, _, _, _, pole, left, right, upper, south⟩ :=
    exists_latitudeNorthFan_support positive small edge
  let longitude := rowMidpoint (latitudeRowSize a 0) edge
  have swap₀ := latitudeSite_inner_reflect θ 0 longitude 0
  have swap₁ := latitudeSite_inner_reflect θ π longitude 0
  rw [sub_zero] at swap₀
  rw [sub_self] at swap₁
  have swap_row (i : ℕ) (valid : i ≤ latitudeStripCount a) (k : ℕ) :
      inner ℝ (latitudeSite (π - θ) longitude) (latitudeRowSite a i k) =
        inner ℝ (latitudeSite θ longitude) (latitudeRowSite a (latitudeStripCount a - i) k) := by
    simpa only [Nat.sub_sub_self valid] using
      latitudeRowSite_inner_reflect positive small (Nat.sub_le (latitudeStripCount a) i) θ longitude k
  have swap_last (k : ℕ) := latitudeRowSite_inner_reflect positive small (Nat.zero_le (latitudeStripCount a))
    θ longitude k
  unfold latitudeSouthChordTriangle
  refine convexHull_subset_frontier_of_latitudeSupport ?_ (π - θ) longitude (cos θ) ?_ ?_
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (Set.mem_insert_of_mem _ rfl)
    · exact latitudeRowSite_mem_sites a le_rfl _
    · exact latitudeRowSite_mem_sites a le_rfl _
  · intro p hp
    rcases hp with poles | ⟨i, valid, k, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at poles
      rcases poles with rfl | rfl
      · exact swap₁.trans_le south.le
      · exact swap₀.trans_le pole.le
    · exact (swap_row i valid k).trans_le (upper _ (Nat.sub_le _ _) k)
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact swap₀.trans pole
    · exact (swap_last edge.val).trans left
    · exact (swap_last (edge.val + 1)).trans right

end Unfoldings.FewestNets
